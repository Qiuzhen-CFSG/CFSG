module
public import Theory.GroupTheory.PushingUp.BaumannBinary.OriginalModule
public import Theory.Representation.SL2.SharpNaturalQuotient
public import Theory.Representation.SL2.TwoSubgroupFixedIndex
public import Glauberman.MaximumAbelianReplacement
public import Glauberman.PushingUpQuadraticOffender
public import Theory.Representation.BinaryOffender.PermutationConjugacy

/-!
# The natural central quotient at binary field degree greater than one

Write V = ⟨Ω₁(Z(P))ᴳ⟩. Its faithful marked action is constructed in
`ActionKernel`. A maximum abelian subgroup outside O₂(G) exists by the
characteristic Sylow obstruction. The representation lower bound and the
maximum-abelian upper bound force its fixed index to equal the field order;
this subgroup therefore supplements O₂(G) in P. Two conjugate Sylows now
have sharp fixed indices, which recognize V/(V ∩ Z(G)) as the natural
module for the original marking. The complete fixed kernel is retained.

This proves the natural-coordinate conclusion of DGS85 (6.3), printed
p.120, for n > 1. It does not prove [O₂(G),G] ≤ V. The argument uses Niles,
*Pushing-up in finite groups* (1979), Lemma 2.9 and the sharp replacement
in 4.3; the actual DGS (6.5) normal-closure application is in
`CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.BaumannApplication.Action`.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace Theory.GroupTheory.BaumannBinary
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]
local instance : Algebra (ZMod 2) F := ZMod.algebra F 2

/-- A maximum abelian subgroup outside the core attains the full field index. -/
theorem sylow_fixed_index (P : Sylow 2 G)
    (hP : NoCharacteristicNormal (P : Subgroup G))
    (V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (hVQ : V ≤ pCore 2 G)
    (q : G →* SL(2,F)) (hq : Function.Surjective q)
    (hk : q.ker = pCore 2 G) (hker : q.ker = centralizer (V : Set G))
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n) :
    (centralizer (P : Set G)).relIndex V = Nat.card F := by
  have hQS : pCore 2 G ≤ (P : Subgroup G) := pCore_isPGroup.le_sylow_of_normal P
  have hVc : V ≤ centralizer (pCore 2 G : Set G) :=
    le_centralizer_iff.mp (hk.symm.trans hker).le
  have hindex := Matrix.SpecialLinearGroup.sylow_core_relIndex q hq hk P
  have hSne : (P : Subgroup G) ≠ ⊥ := by
    intro he
    rw [he,relIndex_bot_right,hF] at hindex
    have hh := Nat.one_lt_pow (by omega : n ≠ 0) (by decide : 1 < (2 : ℕ))
    omega
  have hJ := Glauberman.allAbelianThompson_not_le_normal (P : Subgroup G)
    (pCore 2 G) hQS hSne hP
  have hex : ∃ A : Subgroup G, A ∈ thompsonAbelianSubgroups (P : Subgroup G) ∧
      ¬ A ≤ pCore 2 G := by
    by_contra! hh
    exact hJ (sSup_le hh)
  obtain ⟨A,hA,hout⟩ := hex
  have hlower := Representation.SL2.normal_two_subgroup_fixed_index_lower V q hq hker
    hn hF A (P.isPGroup'.to_le hA.1) (hk.symm ▸ hout)
  have hlower' : (pCore 2 G).relIndex (P : Subgroup G) ≤
      (V ⊓ centralizer (A : Set G)).relIndex V := by
    rw [hindex,inf_relIndex_left]
    exact hlower
  have hi := (Glauberman.maximum_abelian_saturation hA hQS hVQ inferInstance hVc hlower').1
  have hgen := Glauberman.maximum_abelian_supplements_normal hA hQS hVQ inferInstance hVc
    le_normalizer_of_normal hlower'
  have he : V ⊓ centralizer (P : Set G) = V ⊓ centralizer (A : Set G) := by
    change V ⊓ centralizer ((P : Subgroup G) : Set G) = _
    apply le_antisymm (inf_le_inf_left _ (centralizer_le hA.1))
    intro v hv
    refine ⟨hv.1,?_⟩
    have hh : (P : Subgroup G) ≤ centralizer ({v} : Set G) := by
      rw [←hgen]
      apply sup_le
      · intro a ha z hz
        have hzv : z = v := Set.mem_singleton_iff.mp hz
        subst z
        exact (hv.2 a ha).symm
      · intro a ha z hz
        have hzv : z = v := Set.mem_singleton_iff.mp hz
        subst z
        exact (hVc hv.1 a ha).symm
    intro a ha
    exact (hh ha v (Set.mem_singleton v)).symm
  rw [←inf_relIndex_left,he,hi,hindex]

/-- Naturality of the original central quotient at every degree greater than one. -/
theorem centerClosure_natural_quotient_of_kernel (P : Sylow 2 G)
    (hP : NoCharacteristicNormal (P : Subgroup G))
    [IsElementaryAbelian 2 (centerClosure (P : Subgroup G))]
    (hVQ : centerClosure (P : Subgroup G) ≤ pCore 2 G)
    (q : G →* SL(2,F)) (hq : Function.Surjective q)
    (hk : q.ker = pCore 2 G)
    (hker : q.ker = centralizer (centerClosure (P : Subgroup G) : Set G))
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n) :
    let ρ := NormalElementaryQuotient.representation (centerClosure (P : Subgroup G)) q hq hker
    ∃ E : (Additive (centerClosure (P : Subgroup G)) ⧸ fixedSpace ρ ⊤)
        ≃ₗ[ZMod 2] (Fin 2 → F),
      ∀ g v, E (SL2SylowFixedRecognition.centralQuotient ρ g v) = Matrix.mulVec g.val (E v) := by
  let V := centerClosure (P : Subgroup G)
  let ρ := NormalElementaryQuotient.representation V q hq hker
  have hfix := sylow_fixed_index P hP V hVQ q hq hk hker hn hF
  let R := P.mapSurjective hq
  have hdim : fixedCodim ρ R = n := by
    change (centralizer ((P : Subgroup G) : Set G)).relIndex V = _ at hfix
    rw [NormalElementaryQuotient.centralizer_index_eq_fixedCodim V q hq hker,hF] at hfix
    exact Nat.pow_right_injective (by decide : 1 < (2 : ℕ)) hfix
  obtain ⟨g,_,hgen,_⟩ := Matrix.SpecialLinearGroup.exists_residual_generating_sylow_pair
    (MonoidHom.id SL(2,F)) Function.surjective_id (by simpa using (Matrix.SL2.twoCore_eq_bot F).symm) R
  let T := R.mapSurjective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).surjective
  have hdimT : fixedCodim ρ T = n := by
    exact (fixedCodim_map_conj ρ (R : Subgroup SL(2,F)) g).trans hdim
  have hnt : ∃ g, ρ g ≠ 1 := by
    by_contra! he
    have hfixed : fixedSpace ρ R = ⊤ := by
      apply top_unique
      intro v _ r
      change ρ (r : SL(2,F)) v = v
      rw [he]
      rfl
    have hh := fixedCodim_add_finrank ρ (R : Subgroup SL(2,F))
    rw [hfixed,finrank_top,hdim] at hh
    omega
  exact Representation.SL2.sharp_sylow_natural_quotient ρ hnt hn hF R T hgen hdim hdimT
/-- The original DGS hypotheses supply every action-kernel premise above.
The remaining commutator assertion of (6.3) is separate. -/
theorem centerClosure_natural_quotient (P : Sylow 2 G)
    (hc : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (hP : NoCharacteristicNormal (P : Subgroup G))
    (q : G →* SL(2,F)) (hq : Function.Surjective q) (hk : q.ker = pCore 2 G)
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n) :
    letI := (centerClosure_reduced P hc).elementary
    let hker := hk.trans (centerClosure_centralizer P hc hP q hq hk (by omega) hF).symm
    let ρ := NormalElementaryQuotient.representation (centerClosure (P : Subgroup G)) q hq hker
    ∃ E : (Additive (centerClosure (P : Subgroup G)) ⧸ fixedSpace ρ ⊤)
        ≃ₗ[ZMod 2] (Fin 2 → F),
      ∀ g v, E (SL2SylowFixedRecognition.centralQuotient ρ g v) = Matrix.mulVec g.val (E v) := by
  let := (centerClosure_reduced P hc).elementary
  exact centerClosure_natural_quotient_of_kernel P hP (centerClosure_reduced P hc).le_pCore
    q hq hk (hk.trans (centerClosure_centralizer P hc hP q hq hk (by omega) hF).symm)
    hn hF
/-- A surjective natural coordinate map with kernel exactly the original
V ∩ Z(G). Its equivariance uses ambient conjugation and the supplied q. -/
theorem centerClosure_natural_projection (P : Sylow 2 G)
    (hc : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (hP : NoCharacteristicNormal (P : Subgroup G))
    (q : G →* SL(2,F)) (hq : Function.Surjective q) (hk : q.ker = pCore 2 G)
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n) :
    letI := (centerClosure_reduced P hc).elementary
    ∃ f : Additive (centerClosure (P : Subgroup G)) →ₗ[ZMod 2] (Fin 2 → F),
      Function.Surjective f ∧
      LinearMap.ker f = NormalElementaryQuotient.subspace (centerClosure (P : Subgroup G))
        (((centerClosure (P : Subgroup G)) ⊓ center G).subgroupOf
          (centerClosure (P : Subgroup G))) ∧
      ∀ g v, f (Additive.ofMul (MulAut.conjNormal g v.toMul)) =
        Matrix.mulVec (q g).val (f v) := by
  let := (centerClosure_reduced P hc).elementary
  let V := centerClosure (P : Subgroup G)
  have hker := hk.trans (centerClosure_centralizer P hc hP q hq hk (by omega) hF).symm
  let ρ := NormalElementaryQuotient.representation V q hq hker
  obtain ⟨E,hE⟩ := centerClosure_natural_quotient P hc hP q hq hk hn hF
  refine ⟨E.toLinearMap.comp (fixedSpace ρ ⊤).mkQ,
    E.surjective.comp (fixedSpace ρ ⊤).mkQ_surjective,?_,?_⟩
  · rw [←fixedSpace_eq_center P q hq hker]
    ext v
    change E ((fixedSpace ρ ⊤).mkQ v) = 0 ↔ v ∈ fixedSpace ρ ⊤
    rw [map_eq_zero_iff E E.injective]
    exact Submodule.Quotient.mk_eq_zero _
  · intro g v
    have he : ρ (q g) v = Additive.ofMul (MulAut.conjNormal g v.toMul) := by
      apply Additive.toMul.injective
      apply Subtype.ext
      exact NormalElementaryQuotient.representation_apply V q hq hker g v
    change E ((fixedSpace ρ ⊤).mkQ _) = Matrix.mulVec (q g).val (E ((fixedSpace ρ ⊤).mkQ v))
    rw [←he]
    exact hE (q g) ((fixedSpace ρ ⊤).mkQ v)

end Theory.GroupTheory.BaumannBinary
