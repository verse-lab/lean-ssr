/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad
-/
import Mathlib.Data.Finset.Lattice
import Mathlib.Data.Finset.NAry
import Mathlib.Data.Multiset.Functor
import Mathlib.Data.Finset.Image
import Ssreflect.Lang
import Loogle.Find

#align_import data.finset.card from "leanprover-community/mathlib"@"65a1391a0106c9204fe45bc73a039f056558cb83"

/-!
# Cardinality of a finite set

This defines the cardinality of a `Finset` and provides induction principles for finsets.

## Main declarations

* `Finset.card`: `s.card : ℕ` returns the cardinality of `s : Finset α`.

### Induction principles

* `Finset.strongInduction`: Strong induction
* `Finset.strongInductionOn`
* `Finset.strongDownwardInduction`
* `Finset.strongDownwardInductionOn`
* `Finset.case_strong_induction_on`
* `Finset.Nonempty.strong_induction`
-/

universe u

open Function

namespace Finset

/-! ### Functor -/

section Functor

variable {α β : Type u} [∀ P, Decidable P]

variable [∀ P, Decidable P]

protected instance pure : Pure Finset :=
  ⟨fun x => {x}⟩

instance functor : Functor Finset where map f s := s.image f

instance applicative : Applicative Finset :=
  { functor, Finset.pure with
    seq := fun t s => t.sup fun f => (s ()).image f
    seqLeft := fun s t => if t () = ∅ then ∅ else s
    seqRight := fun s t => if s = ∅ then ∅ else t () }

instance lawfulFunctor : LawfulFunctor Finset where
  id_map s := image_id
  comp_map f g s := image_image.symm
  map_const {α} {β} := by simp only [Functor.mapConst, Functor.map]

@[simp]
theorem seq_def (s : Finset α) (t : Finset (α → β)) : t <*> s = t.sup fun f => s.image f :=
  rfl


@[simp]
theorem seqLeft_def (s : Finset α) (t : Finset β) : s <* t = if t = ∅ then ∅ else s :=
  rfl

@[simp]
theorem seqRight_def (s : Finset α) (t : Finset β) : s *> t = if s = ∅ then ∅ else t :=
  rfl

@[simp]
theorem fmap_def {s : Finset α} (f : α → β) : f <$> s = s.image f := rfl

@[simp]
theorem pure_def : (pure : α → Finset α) = singleton := rfl

theorem exists_of_not_empty (t : Finset α) : ¬t = ∅ -> ∃ s, s ∈ t := by sorry

instance lawfulApplicative : LawfulApplicative Finset :=
  { Finset.lawfulFunctor.{u} with
    seqLeft_eq := fun {α} {β} s t => by
      srw seq_def fmap_def seqLeft_def
      scase_if=> [_|hte !a ]
      · srw image_empty; exact (sup_bot _).symm
      · srw mem_sup=> ⟨|[]f /mem_image[][b [hb]<-] /mem_image⟩ //
        move=>/(mem_image_of_mem.{u}) /== /(_ @id α)[?[*]] ⟨//|⟩
        sby apply exists_of_not_empty
    seqRight_eq := fun s t => by
      srw seq_def fmap_def seqRight_def
      scase_if=> [_|hs !a]
      · srw image_empty sup_empty bot_eq_empty
      · srw mem_sup=> ⟨|[]f /mem_image[][b [hb]<-]⟩ //
        move=> hs ⟨//|⟩⟨|⟩ <;> try erw [image_id]=> //
        sby apply mem_image_const_self.2; apply exists_of_not_empty
    pure_seq := fun f s => by simp only [pure_def, seq_def, sup_singleton, fmap_def]
    map_pure := fun f a => image_singleton _ _
    seq_pure := fun s a => sup_singleton'' _ _
    seq_assoc := by
      move=> α β γ s t u !a /=
      simp only [seq_def, exists_prop, mem_sup, mem_image]
      move=> ⟨[g][hg][b][][f][hf][a][ha]<-<-|⟩
      · exact ⟨g ∘ f, ⟨comp g, ⟨g, hg, rfl⟩, f, hf, rfl⟩, a, ha, rfl⟩
      · scase=> c [][]?[][g][hg]<-[f][hf]<-[a][ha]<-
        exact ⟨g, hg, f a, ⟨f, hf, a, ha, rfl⟩, rfl⟩ }

variable [Lattice α] [OrderBot α]

-- theorem PairwiseDisjoint.biUnion_finset' {s : Set ι'} {g : ι' → Finset ι} {f : ι → α}
--     (hs : s.PairwiseDisjoint fun i' : ι' => (g i').sup f)
--     (hg : ∀ i ∈ s, (g i : Set ι).PairwiseDisjoint f) : (⋃ i ∈ s, ↑(g i)).PairwiseDisjoint f := by
--   move; srw Set.mem_iUnion=> a /== c hc ha b d hs hb hab
  -- scase: (eq_or_ne (g c) (g d))=> hcd
  -- -- rintro a ha b hb hab
  -- -- simp_rw [Set.mem_iUnion] at ha hb
  -- obtain hcd | hcd := eq_or_ne (g c) (g d)
  -- · exact hg d hd (by rwa [hcd] at ha) hb hab
  -- · exact (hs hc hd (ne_of_apply_ne _ hcd)).mono (Finset.le_sup ha) (Finset.le_sup hb)

  --         fun x hxa hxb => by
  --         obtain ⟨xa, hfa, rfl⟩ := mem_map.mp hxa
  --         obtain ⟨xb, hfb, hfab⟩ := mem_map.mp hxb
  --         obtain rfl := f.injective hfab
  --         exact disjoint_left.mp (h ha hb hab) hfa hfb :=
  -- eq_of_veq <| Multiset.map_bind _ _ _

/- Card.lean -/

namespace Finset

open Function Multiset Nat

variable {α β R : Type*} {s t : Finset α}
namespace Finset

theorem filter_card_eq' {p : α → Prop} [DecidablePred p] (x : α) :
  (s.filter p).card = s.card -> x ∈ s -> p x := by
  sby move=> /Eq.ge /(eq_of_subset_of_card_le.{u_1}) <-

theorem card_eq_of_bijective' (f : ∀ i, i < n → α) (hf : ∀ a ∈ s, ∃ i, ∃ h : i < n, f i h = a)
    (hf' : ∀ (i) (h : i < n), f i h ∈ s)
    (f_inj : ∀ (i j) (hi : i < n) (hj : j < n), f i hi = f j hj → i = j) : s.card = n := by
  classical
    shave ?: ∀ a : α, a ∈ s ↔ ∃ (i : _) (hi : i ∈ range n), f i (mem_range.1 hi) = a
    { move=> a
        ⟨ /hf [] i [] /mem_range hi <-
          |[] i [] /mem_range /hf' /[swap]->⟩ // }
    -- ⟨fun ha =>
    --     let ⟨i, hi, eq⟩ := hf a ha
    --     ⟨i, mem_range.2 hi, eq⟩,
    --     fun ⟨i, hi, eq⟩ => eq ▸ hf' i (mem_range.1 hi)⟩
    shave -> : s = (range n).attach.image fun i => f i.1 (mem_range.1 i.2)
    { simpa only [ext_iff, mem_image, exists_prop, Subtype.exists, mem_attach, true_and_iff] }
    srw card_image_of_injective ?card_attach //
    sby move=> [i hi] [i hj] /== /f_inj

theorem card_congr' {t : Finset β} (f : ∀ a ∈ s, β) (h₁ : ∀ a ha, f a ha ∈ t)
    (h₂ : ∀ a b ha hb, f a ha = f b hb → a = b) (h₃ : ∀ b ∈ t, ∃ a ha, f a ha = b) :
    s.card = t.card := by
  classical
    srw card_attach.symm
    srw -(card_image_of_injective (f := fun a => f a.1 a.2))
    { srw (congr_arg card) (Finset.ext (s₁ := t))=> ?
      sby srw mem_image=> ⟨/h₃|[a [_ <-]]⟩ }
    sby scase=> a ? [] b ? /== /h₂

theorem card_le_card_of_inj_on' {t : Finset β} (f : α → β) (hf : ∀ a ∈ s, f a ∈ t)
    (f_inj : ∀ a₁ ∈ s, ∀ a₂ ∈ s, f a₁ = f a₂ → a₁ = a₂) : s.card ≤ t.card := by
  classical
    srw -(card_image_of_injOn f_inj)
    sby apply card_le_card; srw image_subset_iff

/-- If there are more pigeons than pigeonholes, then there are two pigeons in the same pigeonhole.
-/

theorem exists_ne_map_eq_of_card_lt_of_maps_to' {t : Finset β} (hc : t.card < s.card) {f : α → β}
    (hf : ∀ a ∈ s, f a ∈ t) : ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ f x = f y := by
  classical
    by_contra! hz
    refine' hc.not_le (card_le_card_of_inj_on f hf _)
    sby move=> ? /hz /[swap] ? /[apply] /[apply]

theorem le_card_of_inj_on_range' (f : ℕ → α) (hf : ∀ i < n, f i ∈ s)
    (f_inj : ∀ i < n, ∀ j < n, f i = f j → i = j) : n ≤ s.card := by
  srw -(card_range n); apply (card_le_card_of_inj_on f)<;> simpa only [mem_range]

theorem surj_on_of_inj_on_of_card_le' {t : Finset β} (f : ∀ a ∈ s, β) (hf : ∀ a ha, f a ha ∈ t)
    (hinj : ∀ a₁ a₂ ha₁ ha₂, f a₁ ha₁ = f a₂ ha₂ → a₁ = a₂) (hst : t.card ≤ s.card) :
    ∀ b ∈ t, ∃ a ha, b = f a ha := by
  classical
    shave ? : (s.attach.image fun a : { a // a ∈ s } => f a a.prop).card = s.card
    { srw card_image_of_injective ?card_attach
      move=> [a₁ ha₁] [a₂ ha₂] /== /hinj // }
    shave<-: image (fun a :{ a // a ∈ s } => f a a.prop) s.attach = t
    { apply eq_of_subset_of_card_le=> //
      sby move=>? /mem_image []/==?/hf }
    srw mem_image=> ? [a [_ <-]] //
