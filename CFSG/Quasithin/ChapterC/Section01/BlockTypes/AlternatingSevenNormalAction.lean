module

public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingSevenCoordinates
public import Theory.SpecificGroups.SymmetricSeven.OddNormalizers
public import Theory.Quasithin.CoprimeRank
public import Theory.Representation.BinaryPermutation.Faithful

/-!
# The whole action on a normal A₇ block

Extend the compatible automorphism coordinates of an ordinary A₇ block to
its actual normal overgroup. The kernel is exactly the centralizer of the
embedded block module, and its restriction to the block is O₂ of the block.
A cubic rank-two subgroup inside the block forces every normalized
two-subgroup to have even image: the normalizer of an odd two-subgroup
of S₇ has cubic rank at most one.

Source application: Aschbacher--Smith, preliminary 15.2.23,
printed p.1115, with binary-core conventions from B.3, refs/quasithin.pdf.
-/

public section
open Subgroup

namespace CFSG.Quasithin.ChapterC
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- The ordinary seven-letter action on the entire normal block module. -/
theorem IsAlternatingBlock.seven_normal_action (X : Subgroup G) [X.Normal]
    (hb : IsAlternatingBlock X 7) :
    ∃ q : (X ⧸ pCore 2 X) ≃* alternatingGroup (Fin 7),
    ∃ E : blockU X ≃* Multiplicative (BinaryPermutation.core (Fin 7)),
    ∃ f : G →* Equiv.Perm (Fin 7),
      (∀ x : X, f x = (q (QuotientGroup.mk' (pCore 2 X) x)).val) ∧
      (∀ g u, (E (MulAut.characteristic (blockU X) (MulAut.conjNormal g) u)).toAdd =
        BinaryPermutation.coreRepresentation (Fin 7) (f g) (E u).toAdd) ∧
      X.map f = alternatingGroup (Fin 7) ∧
      (f.comp X.subtype).ker = pCore 2 X := by
  obtain ⟨q,E,f0,hf0,hE⟩ := hb.seven_automorphism_coordinates
  let f : G →* Equiv.Perm (Fin 7) := f0.comp (MulAut.conjNormal (H := X))
  have hf (x : X) : f x = (q (QuotientGroup.mk' (pCore 2 X) x)).val := by
    change f0 (MulAut.conjNormal (x : G)) = _
    rw [MulAut.conjNormal_val,hf0]
  refine ⟨q,E,f,hf,fun g u => hE _ _,?_,?_⟩
  · apply le_antisymm
    · rintro g ⟨x,hx,rfl⟩
      rw [hf ⟨x,hx⟩]
      exact (q (QuotientGroup.mk' (pCore 2 X) ⟨x,hx⟩)).property
    · intro g hg
      obtain ⟨x,hx⟩ := q.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 X)) ⟨g,hg⟩
      exact ⟨x,x.property,(hf x).trans (congrArg Subtype.val hx)⟩
  · ext x
    change f x = 1 ↔ x ∈ pCore 2 X
    rw [hf]
    constructor
    · intro hx
      apply (QuotientGroup.eq_one_iff (N := pCore 2 X) x).mp
      apply q.injective
      rw [map_one]
      exact Subtype.ext hx
    · intro hx
      have he : QuotientGroup.mk' (pCore 2 X) x = 1 :=
        (QuotientGroup.eq_one_iff (N := pCore 2 X) x).mpr hx
      rw [he,map_one]
      rfl

/-- A rank-two cubic subgroup inside the block forces every normalized
 two-subgroup to have even image in the genuine seven-letter action. -/
theorem seven_normalized_two_image_even {X K Q : Subgroup G}
    (hKX : K ≤ X) (hr : 2 ≤ primeRank 3 K)
    (hQ : IsPGroup 2 Q) (hKQ : K ≤ normalizer (Q : Set G))
    (f : G →* Equiv.Perm (Fin 7))
    (hk : (f.comp X.subtype).ker = pCore 2 X) :
    Q.map f ≤ alternatingGroup (Fin 7) := by
  let g := f.subgroupMap K
  have hker : IsPGroup 2 g.ker := by
    let j : g.ker →* pCore 2 X :=
      ((inclusion hKX).comp g.ker.subtype).codRestrict _ (by
        intro x
        rw [←hk]
        change f (x.val : G) = 1
        exact congrArg Subtype.val x.property)
    apply pCore_isPGroup.of_injective j
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : pCore 2 X => ((z : X) : G)) hxy
  have hc : Nat.Coprime 3 (Nat.card g.ker) := by
    obtain ⟨n,hn⟩ := hker.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  have hrimage : 2 ≤ primeRank 3 (K.map f) :=
    hr.trans (primeRank_le_of_coprime_ker 3 g hc)
  have hn : K.map f ≤ normalizer (Q.map f : Set (Equiv.Perm (Fin 7))) :=
    (map_mono hKQ).trans (le_normalizer_map f)
  by_contra hodd
  have hb := Theory.SpecificGroups.SymmetricSeven.OddNormalizers.normalizer_rank
    (Q.map f) (hQ.map f) hodd
  have hh := hrimage.trans ((primeRank_mono 3 hn).trans hb)
  omega


omit [Finite G] in
theorem seven_action_kernel (X : Subgroup G) [X.Normal]
    (E : blockU X ≃* Multiplicative (BinaryPermutation.core (Fin 7)))
    (f : G →* Equiv.Perm (Fin 7))
    (hE : ∀ g u, (E (MulAut.characteristic (blockU X) (MulAut.conjNormal g) u)).toAdd =
      BinaryPermutation.coreRepresentation (Fin 7) (f g) (E u).toAdd) :
    f.ker = centralizer ((blockU X).map X.subtype : Set G) := by
  have hfaith : Function.Injective (BinaryPermutation.coreRepresentation (Fin 7)) := by
    intro a b hab
    apply BinaryPermutation.naturalRepresentation_injective (Fin 7) (by decide)
    ext v
    obtain ⟨w,rfl⟩ := (BinaryPermutation.coreEquivNatural (Fin 7) (by decide)).surjective v
    rw [←BinaryPermutation.coreEquivNatural_equivariant,
      ←BinaryPermutation.coreEquivNatural_equivariant,hab]
  ext g
  constructor
  · intro hg u hu
    obtain ⟨x,hx,rfl⟩ := hu
    have he := hE g ⟨x,hx⟩
    rw [show f g = 1 from hg,map_one,Module.End.one_apply] at he
    have h := E.injective (Multiplicative.toAdd.injective he)
    have hh := congrArg (fun z : blockU X => ((z : X) : G)) h
    change g * (x : G) * g⁻¹ = x at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  · intro hg
    change f g = 1
    apply hfaith
    ext v
    obtain ⟨u,hu⟩ := E.surjective (Multiplicative.ofAdd v)
    have hv : (E u).toAdd = v := congrArg Multiplicative.toAdd hu
    rw [←hv,←hE]
    have he : MulAut.characteristic (blockU X) (MulAut.conjNormal g) u = u := by
      apply Subtype.ext
      apply Subtype.ext
      change g * ((u : X) : G) * g⁻¹ = u
      rw [←hg u (mem_map_of_mem X.subtype u.property),mul_inv_cancel_right]
    rw [he,map_one,Module.End.one_apply]

end CFSG.Quasithin.ChapterC
