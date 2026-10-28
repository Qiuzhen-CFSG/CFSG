module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.NonEnlargement.Containment
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.AlignedPairs
public import CFSG.Quasithin.Chapter2.Section01To03.LocalStructure.Centers
public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.SourceInputs
public import Theory.GroupTheory.CComponent.CentralInvolution

/-!
# The containing C-component is ordinary

The original central involution z retains its marking in every Gamma-zero
overgroup with the same literal Sylow subgroup S. Source 1.1.5 gives K=[K,z],
centralization of O₂(J), and inversion of O_{2'}(J). The proved moved-component
criterion therefore promotes the unique C-component containing K to an
ordinary component of J=N_G(E). This uses the original maximal two-local
and unique ambient Sylow-overgroup hypotheses, absent from SourceTuple itself.

Source: Aschbacher–Smith 2.5.6, printed p.554, using 1.1.5 and A.3.3.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection.NonEnlargement
universe u
variable {G : Type u} [Group G] [Finite G]
variable {M H K S T E X : Subgroup G} {z : G}

/-- The original z is still the 1.1.5 mark on a Gamma-zero group with Sylow image S. -/
theorem hypotheses115_of_same_sylow
    {κ : GroupClass.{u}} (hG : IsSimpleQTKE κ G)
    (T₀ : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hT₀M : (T₀ : Subgroup G) ≤ M)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T₀ : Subgroup G) ≤ N → N = M)
    (d : SourceTuple M H S T z) (hX : X ∈ gammaZero (Chapter1.He G) M)
    (P : Sylow 2 X) (hP : (P : Subgroup X).map X.subtype = S) :
    Chapter1.Lemma115Hypotheses X P M z := by
  have hSM : S ≤ M := by
    obtain ⟨R,hR⟩ := d.sylow_intersection
    exact hR ▸ (map_subtype_le (R : Subgroup ↥(H ⊓ M))).trans inf_le_right
  obtain ⟨U,HU,hpair,hUS,_⟩ := exists_saturated_pair_aligned hX P (hP ▸ hSM)
  have hzc (x : G) (hx : x ∈ T) : x*z=z*x := by
    obtain ⟨a,ha,rfl⟩ := d.mem_center
    exact congrArg Subtype.val (mem_center_iff.mp ha ⟨x,hx⟩)
  apply lemma_2_3_8_6 hG T₀ hM hT₀M hunique hX hpair P hUS d.involution
    (hP.symm ▸ d.center_le d.mem_center)
  · intro s hs
    exact hzc s (d.lt.le (hP ▸ hs))
  · obtain ⟨R,hR⟩ := d.sylow_maximal
    exact ⟨R,fun x hx => hzc x (hR ▸ hx)⟩

/-- The unique source containing C-component of N(E) is an ordinary component. -/
theorem exists_containing_component
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T₀ : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hT₀M : (T₀ : Subgroup G) ≤ M)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T₀ : Subgroup G) ≤ N → N = M)
    (d : SourceTuple M H S T z) (hK : IsComponentIn K H) (hgen : H = K ⊔ S)
    (hE : E ≠ ⊥) (hEC : E ≤ S ⊓ centralizer (K : Set G))
    (hSE : S ≤ normalizer (E : Set G)) :
    ∃ L : Subgroup G, IsComponentIn L (normalizer (E : Set G)) ∧ K ≤ L := by
  let J := normalizer (E : Set G)
  have hHJ : H ≤ J := normalizes_centralizer_subgroup hgen hEC hSE
  have hKJ : K ≤ J := hK.1.trans hHJ
  obtain ⟨L,⟨hL,hKL⟩,_⟩ := unique_containing_cComponent hG d hK hgen hE hEC hSE
  obtain ⟨hJ,⟨P,hP⟩,_⟩ := centralizer_subgroup_normalizer d hgen hE hEC hSE
  have h115J := hypotheses115_of_same_sylow hG T₀ hM hT₀M hunique d hJ P hP
  have hHgam : H ∈ gamma (Chapter1.He G) M :=
    d.gamma_zero.elim (fun h => h.1.1) (fun h => h.1)
  obtain ⟨R,hR⟩ := d.sylow_intersection
  obtain ⟨Q,hQ⟩ := (intersection_sylow hHgam R).2
  have h115H := hypotheses115_of_same_sylow hG T₀ hM hT₀M hunique d d.gamma_zero Q (hQ.trans hR)
  obtain ⟨_,α,RK,hα,hd,hmoved⟩ := h115H.component_inputs (K.subgroupOf H) hK.2
  rw [map_subgroupOf_eq_of_le hK.1] at hmoved
  let zJ : J := ⟨z,h115J.mem_intersection.1⟩
  have hmovedJ : K.subgroupOf J = ⁅K.subgroupOf J,zpowers zJ⁆ := by
    apply map_injective J.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hKJ,MonoidHom.map_zpowers]
    exact hmoved
  let : IsQuasisimple K := hK.quasisimple
  let : IsQuasisimple (K.subgroupOf J) := IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hKJ).symm
  let : Nontrivial K := (nontrivial_iff_ne_bot K).mpr hK.ne_bot
  let : Nontrivial (K.subgroupOf J) := (subgroupOfEquivOfLe hKJ).surjective.nontrivial
  have hc := component_of_moved_subgroup hL.2 (subgroupOf_mono J hKL) (by
      exact Group.IsPerfect.not_isSolvable (K.subgroupOf J)) zJ hmovedJ
    (fun b hb => Subtype.ext (h115J.central b
      (mem_map_of_mem J.subtype (fitting_pCore_le_sylow P hb))))
    (fun b hb => Subtype.ext (h115J.inverts_oddCore b hb))
  exact ⟨L,⟨hL.1,hc⟩,hKL⟩

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection.NonEnlargement
