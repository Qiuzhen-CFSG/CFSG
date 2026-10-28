module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.MLocal.Structure.QuotientAction
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.MLocal.Structure.QuotientCentralizer.Reduction
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.MLocal.Structure.QuotientCentralizer.LocalKernel
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.MLocal.Structure.QuotientCentralizer.OmegaProjections

/-!
# Cubic centralizers from the two natural quotient constituents

For the actual plane cubic D, this module proves D ≤ I, C_M(V) = P,
C_P(D) = V₁, C_V(D) = V₁, and the full action-image equality
image(C_M(D)) = C(image(D)). The Sylow index first places the cubic in I.
Full displacement of each Omega factor on V then forces its generator to
have nontrivial projections to both factors. Each projection acts without
nonidentity fixed vectors on its natural constituent of P/V, so the
compatible quotient action puts C_P(D) in V. The marked lower action
identifies the fixed plane. Coprime centralizer lifting supplies the image.

`source_quotient_centralizer` uses exactly these earlier source inputs:
T ≤ M and U ≤ T; Y normal in M; C_Y(V) = O₂(Y) from 15.3.49(3);
I = YU from 15.3.54(1); V = Z(P) from 15.3.55; an actual Sylow two-subgroup
of I with ambient image T_K and [T : T_K] = 2 from 15.3.59(2–3);
M = YT from 15.3.59(4); and `NaturalQuotientPair`, retaining the fully
moving Omega factors of 15.3.53(1) and the compatible natural constituents
of 15.3.54(4) with s = 1 from 15.3.58(2). The source choice of g is retained.
The prime-to-three kernel condition follows from these inputs. Normality
of P in I follows from P = O₂(I), and normality of V in P follows from
V = Z(P); neither is replaced by ambient normality.

The earlier inputs remain the responsibility of the source assembly owner.
The symmetric extension and its involution action are separate subsequent
steps; no splitting or fixed-hyperplane assertion is assumed here.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.49(3–4),
15.3.53–55, 15.3.58–59, and the setup of 15.3.60, printed pp.1142, 1146–1150.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.MLocal.Structure
variable {G : Type*} [Group G] {M V : Subgroup G}

namespace NaturalQuotientPair
variable {d : NaturalOrthogonalAction M V}
  {I P : Subgroup G} {hIM : I ≤ M} {hIP : I ≤ normalizer (P : Set G)}
  [(V.subgroupOf P).Normal]
  (r : NaturalQuotientPair d I P hIM hIP)

local instance : MulDistribMulAction OrthogonalPlaneActor OrthogonalPlaneVector :=
  FourGroupMatrixCoordinates.naturalAction

/-- A marked cubic has no nonidentity fixed vector on either natural
constituent of P/V. Full displacement supplies both nontrivial projections. -/
theorem marked_cubic_constituents_fixed_point_free
    (i : OrthogonalPlaneIndex) (a : I) (hpow : a ^ 3 = 1)
    (hne : d.actor ⟨a, hIM a.property⟩ ≠ 1)
    (hcentral : (a : G) ∈ centralizer (d.plane i : Set G)) :
    (∀ w : OrthogonalPlaneVector,
      (r.factors (imageActor d I hIM a)).1 • w = w → w = 1) ∧
    (∀ w : OrthogonalPlaneVector,
      (r.factors (imageActor d I hIM a)).2 • w = w → w = 1) := by
  obtain ⟨hf, hs⟩ := r.cubic_projections_ne_one i a hpow hne hcentral
  exact r.cubic_constituents_fixed_point_free a hpow hf hs

/-- Once the actual plane cubic lies in I, it has a generator of order
three whose projections to both genuine Omega factors are nonidentity. -/
theorem planeCubic_generator_projections [Finite G]
    (hcop : Nat.Coprime 3 (Nat.card ((centralizer (V : Set G)).subgroupOf M)))
    (i : OrthogonalPlaneIndex)
    (PM3 : Sylow 3 (M ⊓ centralizer (d.plane i : Set G) : Subgroup G))
    (hDI : planeCubic M (d.plane i) PM3 ≤ I) :
    ∃ a : I, (a : G) ∈ planeCubic M (d.plane i) PM3 ∧
      zpowers (a : G) = planeCubic M (d.plane i) PM3 ∧ orderOf a = 3 ∧
      (r.factors (imageActor d I hIM a)).1 ≠ 1 ∧
      (r.factors (imageActor d I hIM a)).2 ≠ 1 := by
  obtain ⟨a, ha, hgen, hord, hne⟩ := planeCubic_generator d hcop i PM3
  let b : I := ⟨a, hDI ha⟩
  have hba : inclusion hIM b = a := Subtype.ext rfl
  have horder : orderOf b = 3 := by
    rw [← orderOf_injective (inclusion hIM) (inclusion_injective hIM), hba, hord]
  have hpow : b ^ 3 = 1 := horder ▸ pow_orderOf_eq_one b
  have hbne : d.actor ⟨b, hIM b.property⟩ ≠ 1 := by
    change d.actor (inclusion hIM b) ≠ 1
    rwa [hba]
  obtain ⟨hf, hs⟩ := r.cubic_projections_ne_one i b hpow hbne
    (planeCubic_le_centralizer M (d.plane i) PM3 ha)
  exact ⟨b, ha, hgen, horder, hf, hs⟩

include r in
/-- The actual quotient constituents put C_P(D) inside V, where the marked
lower action identifies it with V₁. No projection premise remains. -/
theorem centralizer_eq_plane [Finite G]
    (hcop : Nat.Coprime 3 (Nat.card ((centralizer (V : Set G)).subgroupOf M)))
    (i : OrthogonalPlaneIndex)
    (PM3 : Sylow 3 (M ⊓ centralizer (d.plane i : Set G) : Subgroup G))
    (hVP : V ≤ P) (hDI : planeCubic M (d.plane i) PM3 ≤ I) :
    P ⊓ centralizer (planeCubic M (d.plane i) PM3 : Set G) = d.plane i := by
  obtain ⟨a, ha, _hgen, hord, hf, hs⟩ := r.planeCubic_generator_projections hcop i PM3 hDI
  exact r.centralizer_eq_plane_of_cubic_projections hcop i PM3 hVP a ha
    (hord ▸ pow_orderOf_eq_one a) hf hs

end NaturalQuotientPair

/-- The kernel and image calculations in the setup of 15.3.60, from the
enumerated earlier source conclusions and the genuine natural quotient pair.
In particular the local placement and centralizer equalities are conclusions,
and all cubic projection premises are discharged. -/
theorem source_quotient_centralizer [Finite G] (T : Sylow 2 G) (M : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M) (d : NaturalOrthogonalAction M (localModule T M))
    (i : OrthogonalPlaneIndex) (g : G) :
    let Z := centralInvolutions T
    let V := localModule T M
    let H := centralizerH Z
    let Y := residualY M H
    let V1 := d.plane i
    let ZS := fixedPlane V (planeStabilizer T V1)
    let U := closureU Z ZS
    let I := pairI Z ZS g
    let P := pairP Z ZS g
    let TK := residualSylow T Z
    ∀ (_hg : g ∈ Y) (_hmoving : ¬ rightConjugate Z g ≤ V ⊓ U)
      (hUT : U ≤ T) (_hMY : M ≤ normalizer (Y : Set G))
      (_hCY : Y ⊓ centralizer (V : Set G) = Stellmacher.twoCoreAmbient Y)
      (hI : I = Y ⊔ U) (_hM : M = Y ⊔ (T : Subgroup G))
      (hcenter : V = (center P).map P.subtype)
      (S : Sylow 2 I) (_hS : (S : Subgroup I).map I.subtype = TK)
      (_hidx : TK.relIndex T = 2),
    let hIM : I ≤ M := hI.le.trans (sup_le (show Y ≤ M from map_subtype_le _) (hUT.trans hTM))
    letI := normal_lower_of_center hcenter
    ∀ (_r : NaturalQuotientPair d I P hIM (pairI_normalizes_pairP Z ZS g))
      (PM3 : Sylow 3 (M ⊓ centralizer (V1 : Set G) : Subgroup G)),
      let D := planeCubic M V1 PM3
      I.relIndex M = 2 ∧ M ⊓ centralizer (V : Set G) = P ∧ D ≤ I ∧
        P ⊓ centralizer (D : Set G) = V1 ∧ fixedPlane V D = V1 ∧
        d.image (M ⊓ centralizer (D : Set G)) =
          centralizer (d.image D : Set OrthogonalActor) := by
  intro Z V H Y V1 ZS U I P TK hg hmoving hUT hMY hCY hI hM hcenter S hS hidx hIM r PM3 D
  let : (V.subgroupOf P).Normal := normal_lower_of_center hcenter
  obtain ⟨hindex, hkernel, hDI⟩ := LocalKernel.source_local_kernel T M hTM d i g
    hg hmoving hUT hMY hCY hI hM hcenter S hS hidx r PM3
  have hp := LocalKernel.action_kernel_isTwoGroup T hTM
    (show Y ≤ M from map_subtype_le _) hMY hM hCY d
  have hcop : Nat.Coprime 3 (Nat.card ((centralizer (V : Set G)).subgroupOf M)) := by
    rw [← d.ker_actor]
    obtain ⟨n, hn⟩ := hp.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  have hVP : V ≤ P := hcenter ▸ map_subtype_le _
  exact ⟨hindex, hkernel, hDI, r.centralizer_eq_plane hcop i PM3 hVP hDI,
    fixedPlane_planeCubic d hcop i PM3, image_centralizer_planeCubic d hcop i PM3⟩

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.MLocal.Structure
