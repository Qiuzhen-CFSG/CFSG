module

public import Stellmacher.SectionTwo.MaximalReplacement
public import Stellmacher.SectionTwo.OmegaCoreReplacementControl

/-!
# The omega-core configuration in Stellmacher (2.3)

For the normal closure E of J(S), write Q = O₂(E). Under the standing
Section Two hypotheses, the core-centralizer equality of (2.3), and the
noncentralizing case, Ω₁Z(J(Q)) is normal in the ambient group. It contains
both Ω₁Z(J(S)) and V(S), and is contained in C(A)V(S) for each maximal
elementary abelian subgroup A of S.

The maximal-elementary replacement C_A(V)V is again maximal in S by the
relative (1.5e) argument. It lies in E and in O₂(G), hence in Q. Conversely,
Q is a normal 2-subgroup of G and therefore centralizes V by the given core
equality. The abstract omega-center replacement-control theorem now applies.
Finally, conjugation invariance of J and characteristicity of its omega-center
establish ambient normality. This formalizes the opening noncentralizing
paragraph of (2.3), Stellmacher, Journal of Algebra 190 (1997), p. 20.
-/

namespace Stellmacher.SectionTwo

/-- The concrete omega-center configuration used in the noncentralizing case of (2.3). -/
public theorem two_three_omega_core_setup
    {G : Type*} [Group G] [Finite G] (h : Hypotheses G) (S : Sylow 2 G)
    (hcore : pCore 2 G = (S : Subgroup G) ⊓ Subgroup.centralizer (vSubgroup S : Set G))
    (hnot : ¬ vSubgroup S ≤ Subgroup.centralizer
      (elementaryAbelianMaxJ (S : Subgroup G) : Set G)) :
    let E := Subgroup.normalClosure (elementaryAbelianMaxJ (S : Subgroup G) : Set G)
    let Z := omegaOneCenterAmbient (elementaryAbelianMaxJ (S : Subgroup G))
    let Z0 := omegaOneCenterAmbient (elementaryAbelianMaxJ (twoCoreAmbient E))
    Z0.Normal ∧ Z ≤ Z0 ∧ vSubgroup S ≤ Z0 ∧
      ∀ A ∈ elementaryAbelianMaxSubgroups (S : Subgroup G),
        Z0 ≤ (Z0 ⊓ Subgroup.centralizer (A : Set G)) ⊔ vSubgroup S := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let V := vSubgroup S
  let J := elementaryAbelianMaxJ (S : Subgroup G)
  let E := Subgroup.normalClosure (J : Set G)
  let Q := twoCoreAmbient E
  let Z0 := omegaOneCenterAmbient (elementaryAbelianMaxJ Q)
  let _ : E.Normal := Subgroup.normalClosure_normal
  let _ : V.Normal := Subgroup.normalClosure_normal
  obtain ⟨hVcore, hVe⟩ := vSubgroup_le_twoCore_and_elementaryAbelian h S
  let _ : IsElementaryAbelian 2 V := hVe
  have hQnormal : Q.Normal := ConjAct.normal_of_characteristic_of_normal
  let _ : Q.Normal := hQnormal
  have hQcore : Q ≤ pCore 2 G := le_sSup ⟨hQnormal,
    (pCore_isPGroup (p := 2) (G := E)).map E.subtype⟩
  have hQS : Q ≤ (S : Subgroup G) := hQcore.trans (fitting_pCore_le_sylow S)
  have hQV : Q ≤ Subgroup.centralizer (V : Set G) := by
    rw [hcore] at hQcore
    exact hQcore.trans inf_le_right
  have hreplace : ∀ A ∈ elementaryAbelianMaxSubgroups (S : Subgroup G),
      (V ⊔ (A ⊓ Subgroup.centralizer (V : Set G))) ∈
        elementaryAbelianMaxSubgroups (S : Subgroup G) ∧
      V ⊔ (A ⊓ Subgroup.centralizer (V : Set G)) ≤ Q := by
    intro A hA
    let K := V ⊔ (A ⊓ Subgroup.centralizer (V : Set G))
    have hK : K ∈ elementaryAbelianMaxSubgroups (S : Subgroup G) :=
      maxElementary_centralizer_replacement h S hnot A hA
    have hKJ : K ≤ J := le_sSup hK
    have hKE : K ≤ E := hKJ.trans Subgroup.le_normalClosure
    have hKcore : K ≤ pCore 2 G := sup_le hVcore (by
      rw [hcore]
      exact le_inf (inf_le_left.trans hA.1) inf_le_right)
    have hRestrict : (pCore 2 G).subgroupOf E ≤ pCore 2 E :=
      le_sSup ⟨inferInstance, (pCore_isPGroup (p := 2) (G := G)).comap_of_injective
        E.subtype E.subtype_injective⟩
    refine ⟨hK, ?_⟩
    change K ≤ (pCore 2 E).map E.subtype
    rw [← Subgroup.map_subgroupOf_eq_of_le hKE]
    exact Subgroup.map_mono ((Subgroup.comap_mono hKcore).trans hRestrict)
  have hVQ : V ≤ Q := by
    obtain ⟨A, hA⟩ := elementaryAbelianMaxSubgroups_nonempty (S : Subgroup G)
    exact (le_sup_left : V ≤ V ⊔ (A ⊓ Subgroup.centralizer (V : Set G))).trans
      (hreplace A hA).2
  have hcontrol := omega_core_replacement_control (S : Subgroup G) Q V hVQ hQS hQV hreplace
  have hJQN : (elementaryAbelianMaxJ Q).Normal := by
    apply Subgroup.normalizer_eq_top_iff.mp
    apply top_unique
    intro g _
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    change (elementaryAbelianMaxJ Q).map (MulAut.conj g).toMonoidHom = elementaryAbelianMaxJ Q
    have hg : g ∈ Subgroup.normalizer (Q : Set G) := by
      rw [Subgroup.normalizer_eq_top]
      trivial
    have hQg := Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
    change Q.map (MulAut.conj g).toMonoidHom = Q at hQg
    rw [← elementaryAbelianMaxJ_map_equiv (MulAut.conj g) Q, hQg]
  let _ : (elementaryAbelianMaxJ Q).Normal := hJQN
  have hZ0normal : Z0.Normal := by
    let W : Subgroup (elementaryAbelianMaxJ Q) :=
      (omega₁ (Subgroup.center (elementaryAbelianMaxJ Q)) (p := 2)).map
        (Subgroup.center (elementaryAbelianMaxJ Q)).subtype
    let _ : (omega₁ (Subgroup.center (elementaryAbelianMaxJ Q)) (p := 2)).Characteristic :=
      omega₁_characteristic (Subgroup.center (elementaryAbelianMaxJ Q))
    let _ : W.Characteristic := inferInstance
    exact ConjAct.normal_of_characteristic_of_normal
  exact ⟨hZ0normal, hcontrol⟩

end Stellmacher.SectionTwo
