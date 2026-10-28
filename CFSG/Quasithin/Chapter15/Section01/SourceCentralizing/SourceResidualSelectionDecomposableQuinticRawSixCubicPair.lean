module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawSixCubicPreimages
public import Theory.SpecificGroups.AlternatingSix.NaturalCubicGeneration
public import Theory.SpecificGroups.SymmetricSix.ResidualPairRecognition.ComponentLocals
public import Theory.GroupAction.PerfectCentralQuotient
public import Theory.GroupTheory.SubgroupPartitionCounting

/-!
# The native parabolic pair in the full cubic cover

The two incident A₆ parabolics lift canonically to S₄ subgroups of the same
perfect central three-cover. They contain the chosen Sylow two-subgroup
and generate the whole cover. Their invariance is stated for the actual
central-quotient action: natural automorphisms preserving that Sylow fix
each lifted subgroup. Source naturality must still be proved separately.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section01.RawSixCubicSplit
open Theory.SpecificGroups.SymmetricSix
variable {X : Type*} [Group X] [Finite X] [Group.IsPerfect X]

private theorem native_parabolic_model (S : Sylow 2 A6) (J : Subgroup A6)
    (hSJ : (S : Subgroup A6) ≤ J) (hi : (S : Subgroup A6).relIndex J = 3) :
    Nonempty (J ≃* Equiv.Perm (Fin 4)) := by
  obtain ⟨g,hg,hall⟩ := a6_coatoms_over_sylow S
  have hS : Nat.card S = 8 := by
    rw [Sylow.card_eq_multiplicity,nat_card_alternatingGroup,Nat.card_fin]
    decide +kernel
  have hJ : Nat.card J = 24 := by
    have hh := relIndex_mul_card_of_le hSJ
    rw [hS,hi] at hh
    exact hh.symm
  have hne : J ≠ ⊤ := by
    intro he
    rw [he,Nat.card_congr Subgroup.topEquiv.toEquiv,nat_card_alternatingGroup] at hJ
    norm_num [Nat.factorial] at hJ
  obtain ⟨P,hP,hJP⟩ := (eq_top_or_exists_le_coatom J).resolve_left hne
  have hm : Nonempty (P ≃* Equiv.Perm (Fin 4)) := by
    rcases (hall P).mp ⟨hP,hSJ.trans hJP⟩ with he | he
    · exact ⟨(MulEquiv.subgroupCongr he).trans
        (((MulAut.conj g).subgroupMap a6DuadStabilizer).symm.trans a6DuadModelEquiv.symm)⟩
    · exact ⟨(MulEquiv.subgroupCongr he).trans
        (((MulAut.conj g).subgroupMap a6SynthemeStabilizer).symm.trans
          ResidualPairRecognition.ComponentLocals.edgeEquiv.symm)⟩
  obtain ⟨b⟩ := hm
  have hcardP : Nat.card P = 24 := by
    rw [Nat.card_congr b.toEquiv,Nat.card_perm]
    norm_num
  have he : J = P := eq_of_le_of_card_ge hJP (by omega)
  exact ⟨(MulEquiv.subgroupCongr he).trans b⟩

omit [Finite X] [Group.IsPerfect X] in
private theorem preimage_preserved
    {Y : Type*} [Group Y] (f : X →* Y) (a : MulAut X) (b : MulAut Y)
    (hab : ∀ x, f (a x) = b (f x)) (J : Subgroup Y)
    (hJ : J.map b.toMonoidHom = J) :
    (J.comap f).map a.toMonoidHom = J.comap f := by
  apply le_antisymm
  · rintro x ⟨y,hy,rfl⟩
    change f (a y) ∈ J
    rw [hab,←hJ]
    exact mem_map_of_mem b.toMonoidHom hy
  · intro x hx
    refine ⟨a.symm x,?_,a.apply_symm_apply x⟩
    have hh : b (f (a.symm x)) = f x := (hab (a.symm x)).symm.trans
      (congrArg f (a.apply_symm_apply x))
    have hmem : b (f (a.symm x)) ∈ J := hh ▸ hx
    rw [←hJ] at hmem
    obtain ⟨y,hy,hyx⟩ := hmem
    change f (a.symm x) ∈ J
    exact b.injective hyx ▸ hy

/-- Canonical S₄ parabolics in a perfect central three-cover of A₆.
The invariance clause uses the literal quotient action and same Sylow. -/
theorem central_cover_pair
    (e : (X ⧸ center X) ≃* A6) (hcenter : IsPGroup 3 (center X))
    (S : Sylow 2 X) :
    ∃ P Q : Subgroup X,
      (S : Subgroup X) ≤ P ∧ (S : Subgroup X) ≤ Q ∧ P ⊔ Q = ⊤ ∧
      Nonempty (P ≃* Equiv.Perm (Fin 4)) ∧
      Nonempty (Q ≃* Equiv.Perm (Fin 4)) ∧
      ∀ a : MulAut X,
        MulAut.centralQuotientAction e a ∈ _root_.AlternatingSix.ShadowLocal.natural →
        (S : Subgroup X).map a.toMonoidHom = S →
        P.map a.toMonoidHom = P ∧ Q.map a.toMonoidHom = Q := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center X))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = center X := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  let S' := S.mapSurjective hf
  obtain ⟨J,K,hJ,hK,hJi,hKi,hgen,hinv⟩ :=
    _root_.AlternatingSix.NaturalCubicGeneration.invariant_cubic_pair S'
  obtain ⟨eJ⟩ := native_parabolic_model S' J hJ hJi
  obtain ⟨eK⟩ := native_parabolic_model S' K hK hKi
  let P := (pResidual 3 (J.comap f)).map (J.comap f).subtype
  let Q := (pResidual 3 (K.comap f)).map (K.comap f).subtype
  obtain ⟨hP,⟨bP⟩,hSP,_⟩ := preimage_residual f hf hk.le (hk ▸ hcenter) J eJ
  obtain ⟨hQ,⟨bQ⟩,hSQ,_⟩ := preimage_residual f hf hk.le (hk ▸ hcenter) K eK
  refine ⟨P,Q,hSP S S.isPGroup' (map_le_iff_le_comap.mp hJ),
    hSQ S S.isPGroup' (map_le_iff_le_comap.mp hK),
    preimage_residuals_generate f hf hk.le (hk ▸ hcenter) J K eJ eK hgen,
    ⟨bP.trans eJ⟩,⟨bQ.trans eK⟩,?_⟩
  intro a ha hS
  let b := MulAut.centralQuotientAction e a
  have hab : ∀ x, f (a x) = b (f x) := fun x =>
    (MulAut.centralQuotientAction_apply e a x).symm
  have hSb : (S' : Subgroup A6).map b.toMonoidHom = S' := by
    change ((S : Subgroup X).map f).map b.toMonoidHom = (S : Subgroup X).map f
    rw [map_map]
    have hh : b.toMonoidHom.comp f = f.comp a.toMonoidHom := MonoidHom.ext fun x => (hab x).symm
    rw [hh,←map_map,hS]
  obtain ⟨hj,hk'⟩ := hinv b ha hSb
  constructor
  · change ((pResidual 3 (J.comap f)).map (J.comap f).subtype).map a.toMonoidHom = P
    rw [map_embedded_pResidual,preimage_preserved f a b hab J hj]
  · change ((pResidual 3 (K.comap f)).map (K.comap f).subtype).map a.toMonoidHom = Q
    rw [map_embedded_pResidual,preimage_preserved f a b hab K hk']

end CFSG.Quasithin.Chapter15.Section01.RawSixCubicSplit
