module
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.NativeSource16.Eight
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.NativeSource16.OddResidual.Source

/-!
# Recognition at the corrected terminal distinguished base

Conjugate t into M. The original odd residual fixes two distinct cosets,
so the odd-normalizer theorem prevents its conjugate from lying in M:
otherwise it would centralize t and its full commutator would be trivial.
The conjugated centralizer therefore crosses M. The proved solvable-circle
alternative forces this circle to be nonsolvable, and proper-subgroup
induction supplies its perfect odd central cover and genuine Bender model.

This replaces the invalid original-z containment at the end of GLS IV,
Chapter 2, Proposition 16.5 (printed page 86). No original distinguished
involution of M is asserted to centralize the original tuv.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1 Subgroup
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

omit [Finite G] in
public theorem residual_conjugate_not_le_base
    (h : IsProductDisconnected Z M) (ha : ResidualAction Z M)
    {t : G} (ht : t∈Z) (htM : t∉M) (R : Subgroup G)
    (hodd : Odd (Nat.card R)) (hRD : R≤residualPairStabilizer M t)
    (htR : t∈normalizer R) (hrep : ⁅R,zpowers t⁆=R) (hn : ¬IsCyclic R)
    (g : G) (hgtM : MulAut.conj g t∈M) :
    ¬ R.map (MulAut.conj g).toMonoidHom ≤ M := by
  let e := MulAut.conj g
  let Q := R.map e.toMonoidHom
  let z := e t
  have hz : z∈Z := h.invariant g t ht
  have hQodd : Odd (Nat.card Q) := by
    rwa [card_map_of_injective e.injective]
  have hzQ : z∈normalizer Q := by
    rw [← map_equiv_normalizer_eq]
    exact mem_map_of_mem e.toMonoidHom htR
  intro hQM
  rcases ha.odd_normalizer z hz hgtM Q hQodd hQM hzQ with hQc | hunique
  · have hRc : R≤centralizer ({t}:Set G) := by
      intro x hx
      apply mem_centralizer_singleton_iff.mpr
      apply e.injective
      exact (map_mul e x t).trans
        ((mem_centralizer_singleton_iff.mp (hQc (mem_map_of_mem e.toMonoidHom hx))).trans
          (map_mul e t x).symm)
    have hbot : R=⊥ := by
      rw [← hrep,commutator_eq_bot_iff_le_centralizer,zpowers_eq_closure,centralizer_closure]
      exact hRc
    exact hn (hbot ▸ inferInstance)
  · let α : G⧸M := QuotientGroup.mk 1
    let β : G⧸M := t • α
    have hne : α≠β := by
      intro hh
      apply htM
      have hh' : t∈MulAction.stabilizer G α := MulAction.mem_stabilizer_iff.mpr hh.symm
      rwa [baseCoset_stabilizer] at hh'
    have hRα : R≤MulAction.stabilizer G α := by
      rw [baseCoset_stabilizer]
      exact hRD.trans inf_le_left
    have hRβ : R≤MulAction.stabilizer G β := by
      have hs : MulAction.stabilizer G β=rightConjugate M t := by
        simpa [β,α,MulAction.Quotient.smul_mk,smul_eq_mul,(h.involutions t ht).inv_eq_self]
          using conjugateCoset_stabilizer M t
      rw [hs]
      exact hRD.trans inf_le_right
    have hQα : Q≤MulAction.stabilizer G (g • α) := by
      rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj]
      exact map_mono hRα
    have hQβ : Q≤MulAction.stabilizer G (g • β) := by
      rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj]
      exact map_mono hRβ
    have he : g • α=g • β := (hunique _ hQα).trans (hunique _ hQβ).symm
    exact hne (MulAction.injective g he)

public theorem source16_final_circle_conjugate_recognition
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) {t u w : G}
    (ht : t∈Z) (htM : t∉M)
    (hu : PFAppendixIII.IsInvolution u) (huD : u∈residualPairStabilizer M t)
    (hw : PFAppendixIII.IsInvolution w) (htw : Commute t w)
    (R : Subgroup G) (hodd : Odd (Nat.card R))
    (hRD : R≤residualPairStabilizer M t) (hRw : R≤centralizer ({w}:Set G))
    (htR : t∈normalizer R) (hrep : ⁅R,zpowers t⁆=R) (hn : ¬IsCyclic R) :
    ∃ g : G, let e := MulAut.conj g
      let B := centralizer ({e w}:Set G)
      let C := localCircle Z B
      e t∈M ∧ e w∈M ∧ ¬B≤M ∧ ¬Group.IsSolvable C ∧
        ∃ n : ℕ, 2≤n ∧ commutator C=⊤ ∧ Odd (Nat.card (center C)) ∧
          IsSimpleBenderGroupAtExponent n (C⧸center C) := by
  obtain ⟨z,hz,hzM⟩ := h.disconnected.nonempty
  obtain ⟨g,hg⟩ := isConj_iff.mp (r.one_class t ht z hz)
  let e := MulAut.conj g
  have het : e t=z := hg
  have hgtM : e t∈M := het.symm ▸ hzM
  have hzw : Commute z (e w) := by
    rw [←het]
    exact htw.map e.toMonoidHom
  have hgwM : e w∈M := mem_of_commute h.disconnected hz hzM hzw
  have hwi : PFAppendixIII.IsInvolution (e w) :=
    IsInvolution.map_of_injective hw e.toMonoidHom e.injective
  let B := centralizer ({e w}:Set G)
  have hne : ∃ z∈Z,z∈B ∧ z∈M :=
    ⟨z,hz,mem_centralizer_singleton_iff.mpr hzw.eq,hzM⟩
  have hRB : R.map e.toMonoidHom≤B := by
    rintro x ⟨y,hy,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    exact (Commute.map (mem_centralizer_singleton_iff.mp (hRw hy)) e.toMonoidHom).eq
  have hBM : ¬B≤M := fun hle => residual_conjugate_not_le_base h.disconnected ha
    ht htM R hodd hRD htR hrep hn g hgtM (hRB.trans hle)
  have hns : ¬Group.IsSolvable (localCircle Z B) := fun hsol =>
    hBM (source16_solvable_centralizer_le h r ha ht htM hu huD hwi hgwM hsol)
  obtain ⟨hc,hperfect,hmodel,_⟩ := localCircle_nonsolvable_structure h r ha B
    (r.involution_centralizer_ne_top h.disconnected hwi) hBM hne hns
  obtain ⟨n,hnn,hnmodel⟩ := hmodel.exists_exponent
  have hcenter : Odd (Nat.card (center (localCircle Z B))) := by
    rw [←hc]
    exact Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2))
  exact ⟨g,hgtM,hgwM,hBM,hns,n,hnn,hperfect,hcenter,hnmodel⟩

end BenderSuzuki.ZD
