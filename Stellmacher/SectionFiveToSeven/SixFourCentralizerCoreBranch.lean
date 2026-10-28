module
public import Stellmacher.SectionFiveToSeven.SixFourCentralizerFactor
public import Stellmacher.SectionThree.ThompsonCoreResidualCentralizer
public import Theory.GroupTheory.SylowNormalSupplementIntersection

/-!
# The Thompson-in-core branch of centralizer factor selection

Under Hypothesis Two, suppose J(S) lies in O₂(P₂), w is a nonidentity
member of Ω₁(Z(J(S))), and C_{P₂}(w) together with S generates P₂. Then
there is a local-family member F in C_{P₂}(w), over C_S(w), which generates
P₂ with S and satisfies [O²(F), B(S)] = O²(F).

The Thompson-core residual centralizer theorem puts O²(P₂) inside
C_{P₂}(w). The normal residual supplements the given Sylow subgroup,
so normal-supplement Sylow transfer makes C_S(w) Sylow in C_{P₂}(w).
The central involution w gives this centralizer a nontrivial 2-core.
The shared extraction theorem then uses Baumann heredity, (6.1), and (3.4)
to obtain the generating factor and its residual commutator equality.

This is an explicit conditional branch of the factor selection in
Stellmacher (6.4), Journal of Algebra 190 (1997), p.32;
source: `refs/latex/stellmacher-n-group.tex`. Its extra Thompson-core
hypothesis must be discharged when applying it to the unrestricted result.
-/

namespace Stellmacher.SectionsFiveToSeven
universe u

private theorem centralizer_core_ne_bot
    {H : Type u} [Group H] [Finite H]
    (P : Subgroup H) (w : H) (hwP : w ∈ P) (hw2 : w ^ 2 = 1) (hwne : w ≠ 1) :
    twoCoreIn (P ⊓ Subgroup.centralizer ({w} : Set H)) ≠ ⊥ := by
  let C := P ⊓ Subgroup.centralizer ({w} : Set H)
  have hwC : w ∈ C := ⟨hwP, Subgroup.mem_centralizer_iff.mpr (by
    intro x hx
    have heq : x = w := Set.mem_singleton_iff.mp hx
    subst x
    rfl)⟩
  let x : C := ⟨w, hwC⟩
  have hxcent : x ∈ Subgroup.center C := by
    apply Subgroup.mem_center_iff.mpr
    intro y
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp y.property.2 w rfl).symm
  let Q := Subgroup.zpowers x
  have hQcent : Q ≤ Subgroup.center C := Subgroup.zpowers_le.mpr hxcent
  let _ : Q.Normal := ⟨fun q hq c => by
    have heq := Subgroup.mem_center_iff.mp (hQcent hq) c
    simpa [heq, mul_assoc] using hq⟩
  have hx2 : x ^ 2 = 1 := Subtype.ext hw2
  have hQp : IsPGroup 2 Q := (IsElementaryAbelian.zpowers_of_pow_eq_one (p := 2) hx2).isPGroup 2 _
  have hQcore : Q ≤ pCore 2 C := le_sSup ⟨inferInstance, hQp⟩
  intro hbot
  have hwcore : w ∈ twoCoreIn C :=
    Subgroup.mem_map_of_mem C.subtype (hQcore (Subgroup.mem_zpowers x))
  rw [show twoCoreIn C = ⊥ from hbot] at hwcore
  exact hwne hwcore

private theorem centralizer_sylow_of_residual_centralizes
    {H : Type u} [Group H] [Finite H]
    (S P : Subgroup H) (hSyl : IsSylowTwoIn S P)
    (w : H) (hR : twoResidualAmbient P ≤ Subgroup.centralizer ({w} : Set H)) :
    IsSylowTwoIn (S ⊓ Subgroup.centralizer ({w} : Set H))
      (P ⊓ Subgroup.centralizer ({w} : Set H)) := by
  let C := P ⊓ Subgroup.centralizer ({w} : Set H)
  let T := S ⊓ Subgroup.centralizer ({w} : Set H)
  have hTC : T ≤ C := inf_le_inf_right _ hSyl.1
  obtain ⟨hSP, R, hRS⟩ := hSyl
  let C0 := C.subgroupOf P
  let N := twoResidualSubgroup P
  let _ : N.Normal := by
    dsimp [N, twoResidualSubgroup]
    rw [sInf_eq_iInf]
    exact Subgroup.normal_iInf_normal fun K => Subgroup.normal_iInf_normal fun hK => hK.1
  have hNmap : N.map P.subtype = twoResidualAmbient P := rfl
  have hNC : N ≤ C0 := by
    intro n hn
    exact ⟨n.property, hR (Subgroup.mem_map_of_mem P.subtype hn)⟩
  have hNS : N ⊔ (R : Subgroup P) = ⊤ := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_sup, hNmap, hRS, SectionThree.twoResidual_sup_sylowImage ⟨R, hRS⟩,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  obtain ⟨U, hU⟩ := R.exists_map_eq_inf_of_normal_supplement N C0 hNS hNC
  let e : C0 ≃* C := Subgroup.subgroupOfEquivOfLe inf_le_left
  have he : Function.Surjective e.toMonoidHom := e.surjective
  let U' : Sylow 2 C := U.mapSurjective he
  refine ⟨hTC, U', ?_⟩
  dsimp only [U']
  rw [Sylow.coe_mapSurjective, Subgroup.map_map]
  have hcomp : C.subtype.comp e.toMonoidHom = P.subtype.comp C0.subtype := by
    ext x
    rfl
  rw [hcomp, ← Subgroup.map_map, hU, Subgroup.map_inf _ _ _ P.subtype_injective,
    hRS, Subgroup.map_subgroupOf_eq_of_le inf_le_left]
  change S ⊓ (P ⊓ Subgroup.centralizer ({w} : Set H)) = T
  rw [← inf_assoc, inf_eq_left.mpr hSP]

public theorem sixFour_centralizer_factor_of_thompson_le_core
    {H : Type u} [Group H] [Finite H]
    (S0 : Sylow 2 H) (S P1 P2 : Subgroup H)
    (h : HypothesisTwo H S0 S P1 P2) (w : H)
    (hwZJ : w ∈ omegaOneCenterAmbient (elementaryAbelianMaxJ S))
    (hwne : w ≠ 1) (hJcore : elementaryAbelianMaxJ S ≤ twoCoreIn P2)
    (hgen : (P2 ⊓ Subgroup.centralizer ({w} : Set H)) ⊔ S = P2) :
    ∃ F : Subgroup H,
      F ∈ PFamily (P2 ⊓ Subgroup.centralizer ({w} : Set H))
        (S ⊓ Subgroup.centralizer ({w} : Set H)) ∧
      F ⊔ S = P2 ∧ ⁅twoResidualAmbient F, baumannIn S⁆ = twoResidualAmbient F := by
  have hR := SectionThree.residual_centralizes_thompson_omega_of_le_twoCore
    S h.sectionThreeHypotheses P2 ((pFamily_iff_pSet ⊤ S P2).mp h.fiveOne.P2_mem)
    (lemma_five_three S0 S P1 P2 h).2.2.1 (lemma_six_one S0 S P1 P2 h) hJcore
  have hRc : twoResidualAmbient P2 ≤ Subgroup.centralizer ({w} : Set H) := by
    intro r hr
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hxw : x = w := Set.mem_singleton_iff.mp hx
    subst x
    exact Subgroup.mem_centralizer_iff.mp (hR hr) w hwZJ
  have hSyl := centralizer_sylow_of_residual_centralizes S P2 h.fiveOne.P2_mem.1.2.1 w hRc
  have hwJS : elementaryAbelianMaxJ S ≤ S := sSup_le fun _ hA => hA.1
  have hwS : w ∈ S := hwJS ((mem_omegaOneCenterAmbient_iff _ _).mp hwZJ).1
  have hwP : w ∈ P2 := h.fiveOne.P2_mem.1.2.1.1 hwS
  have hw2 : w ^ 2 = 1 := ((mem_omegaOneCenterAmbient_iff _ _).mp hwZJ).2.1
  have hBT : baumannIn S ≤ S ⊓ Subgroup.centralizer ({w} : Set H) := by
    refine le_inf inf_le_left ?_
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hxw : x = w := Set.mem_singleton_iff.mp hx
    subst x
    exact Subgroup.mem_centralizer_iff.mp hb.2 w hwZJ
  exact sixFour_generating_factor_of_sylow S0 S P1 P2 h _ _ inf_le_left hBT hSyl
    (centralizer_core_ne_bot P2 w hwP hw2 hwne) inf_le_left hgen

end Stellmacher.SectionsFiveToSeven
