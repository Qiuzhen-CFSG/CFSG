module

public import Theory.AtlasPort.LinearGroups.G2.LieShortParabolic.Geometry

/-!
# The full short parabolic in even-field G₂

The five-root short radical remains the intrinsic two-core after adjoining the
split torus. The concrete null-plane geometry and root coordinates show that an
element of the full short parabolic centralizing this radical lies in the
Borel; the C and D root commutator equations kill both torus scalars, and the
E root equation kills the sixth unipotent coordinate. Thus the radical is
self-centralizing intrinsically inside the full parabolic. Normalization and
the ambient core equality reuse the short-local development. The centralizer
calculation holds over any characteristic-two field; the two-core statements
require only finiteness, including the full binary model.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, Theorem
0.1.2(1), printed pp.3–4, and F.1.12(I)(3), pp.262–264. Coordinate formulas
come from the licensed ATLAS port; see LICENSES/ATLAS.txt and
LICENSES/ATLAS-CITATION.cff.
-/

open Atlas.G2 Atlas.G2.Explicit Atlas.G2.LieParabolicSetup Atlas.SplitOctonion
namespace Atlas.G2.EvenLocal
variable {F : Type*} [Field F] [CharP F 2]

private theorem borel_of_commute_rootB (g : parabolic₁ (F := F))
    (hb : Commute g.val (rootB 1)) : g.val ∈ borel := by
  have hp := parabolic₁_le_shortPlaneStabilizer g.property
  have hplane := shortPlane_coordinates
    (hp.1 (basisVector 0) (basis_mem_shortPlane 0 (by decide)))
  have hroot : (rootB (1 : F)).val (basisVector 5) =
      basisVector 5 + basisVector 0 := by
    funext i
    fin_cases i <;>
      simp [rootB, rootBEquiv, rootBLinear, rootBApply, basisVector,
        CharTwo.neg_eq]
  have h := congrArg (fun r : Model F => r.val (basisVector 5) 1) hb.eq
  change g.val.val ((rootB (1 : F)).val (basisVector 5)) 1 =
    (rootB (1 : F)).val (g.val.val (basisVector 5)) 1 at h
  rw [hroot, map_add] at h
  have h1 : g.val.val (basisVector 0) 1 = 0 := by
    simpa [rootB, rootBEquiv, rootBLinear, rootBApply] using h
  have he : g.val.val (basisVector 0) =
      g.val.val (basisVector 0) 0 • basisVector 0 := by
    rw [hplane, h1]
    funext i
    fin_cases i <;> simp [basisVector]
  have h0 : g.val.val (basisVector 0) 0 ≠ 0 := by
    intro hz
    have hz' : g.val.val (basisVector 0) = 0 := by
      rw [he, hz, zero_smul]
    exact first_basis_ne_zero (g.val.val.injective (hz'.trans (map_zero _).symm))
  have hl : g.val ∈ parabolic₂ := by
    change g.val ∈ parabolic
    rw [parabolic_eq_pointStabilizer]
    exact (mem_pointStabilizer_iff _).mpr ⟨Units.mk0 _ h0, he⟩
  exact parabolics_intersection.le ⟨g.property, hl⟩

private theorem borel_torus_trivial (t : Fin 6 → F) (l m : Fˣ)
    (hc : Commute (unipotentProduct t * torus l m) (rootC 1))
    (hd : Commute (unipotentProduct t * torus l m) (rootD 1)) :
    l = 1 ∧ m = 1 := by
  have hl := congrArg (fun g : Model F => g.val (basisVector 3) 0) hc.eq
  have hm := congrArg (fun g : Model F => g.val (basisVector 3) 1) hd.eq
  simp [unipotentProduct, rootA, rootB, rootC, rootD, rootE, rootF,
    rootAEquiv, rootBEquiv, rootCEquiv, rootDEquiv, rootEEquiv, rootFEquiv,
    rootALinear, rootBLinear, rootCLinear, rootDLinear, rootELinear, rootFLinear,
    rootAApply, rootBApply, rootCApply, rootDApply, rootEApply, rootFApply,
    torus, torusEquiv, torusLinear, torusWeights, basisVector,
    CharTwo.neg_eq, CharTwo.sub_eq_add] at hl hm
  constructor
  · apply Units.ext
    change (l : F) = 1
    linear_combination hl
  · apply Units.ext
    change (m : F) = 1
    linear_combination hm

private theorem borel_sixth_zero (t : Fin 6 → F)
    (he : Commute (unipotentProduct t) (rootE 1)) : t 5 = 0 := by
  have h := congrArg (fun g : Model F => g.val (basisVector 2) 0) he.eq
  simp [unipotentProduct, rootA, rootB, rootC, rootD, rootE, rootF,
    rootAEquiv, rootBEquiv, rootCEquiv, rootDEquiv, rootEEquiv, rootFEquiv,
    rootALinear, rootBLinear, rootCLinear, rootDLinear, rootELinear, rootFLinear,
    rootAApply, rootBApply, rootCApply, rootDApply, rootEApply, rootFApply,
    basisVector, CharTwo.neg_eq, CharTwo.sub_eq_add] at h
  linear_combination h

/-- The five-root radical is self-centralizing inside the full short parabolic. -/
public theorem short_radical_selfCentralizing :
    Subgroup.centralizer ((radical₁ (F := F)).subgroupOf parabolic₁ :
      Set (parabolic₁ (F := F))) ≤ radical₁.subgroupOf parabolic₁ := by
  intro g hg
  have hle : radical₁ (F := F) ≤ parabolic₁ :=
    (fiveRootSubgroup_le_unipotent _ _).trans (le_trans le_sup_left le_sup_left)
  have hc (r : Model F) (hr : r ∈ radical₁) : Commute g.val r := by
    exact (congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hg
      ⟨r, hle hr⟩ hr)).symm
  have hb := hc (rootB 1)
    ⟨![0, 1, 0, 0, 0, 0], rfl, by simp [unipotentProduct]⟩
  have hC := hc (rootC 1)
    ⟨![0, 0, 1, 0, 0, 0], rfl, by simp [unipotentProduct]⟩
  have hd := hc (rootD 1)
    ⟨![0, 0, 0, 1, 0, 0], rfl, by simp [unipotentProduct]⟩
  have he := hc (rootE 1)
    ⟨![0, 0, 0, 0, 1, 0], rfl, by simp [unipotentProduct]⟩
  have hgB := borel_of_commute_rootB g hb
  obtain ⟨⟨⟨u, hu⟩, ⟨v, hv⟩⟩, hfactor⟩ :=
    (borelProductEquiv (K := F)).surjective ⟨g.val, hgB⟩
  have hfactor' : u * v = g.val := congrArg Subtype.val hfactor
  rw [unipotent_eq_range] at hu
  obtain ⟨t, rfl⟩ := hu
  obtain ⟨⟨l, m⟩, rfl⟩ := hv
  change unipotentProduct t * torus l m = g.val at hfactor'
  rw [← hfactor'] at hC hd he
  obtain ⟨rfl, rfl⟩ := borel_torus_trivial t l m hC hd
  have htor : torus (1 : Fˣ) 1 = 1 := (torusHom (K := F)).map_one
  rw [htor, mul_one] at he hfactor'
  change g.val ∈ radical₁
  exact ⟨t, borel_sixth_zero t he, hfactor'⟩

/-- The full short parabolic normalizes its five-root radical. -/
public theorem parabolic₁_le_normalizer_radical₁ :
    parabolic₁ (F := F) ≤
      Subgroup.normalizer (radical₁ (F := F) : Set (Model F)) :=
  parabolic₁_normalizes_radical₁

/-- The ambient image of the intrinsic two-core is the concrete radical. -/
public theorem parabolic₁_pCoreIn [Finite F] :
    (parabolic₁ (F := F)).pCoreIn 2 = radical₁ :=
  LieParabolicSetup.parabolic₁_pCore

/-- The intrinsic two-core of the full short parabolic is the subgroupOf radical. -/
public theorem parabolic₁_pCore [Finite F] :
    pCore 2 (parabolic₁ (F := F)) = radical₁.subgroupOf parabolic₁ := by
  apply Subgroup.map_injective (parabolic₁ (F := F)).subtype_injective
  change (parabolic₁ (F := F)).pCoreIn 2 = _
  have hle : radical₁ (F := F) ≤ parabolic₁ :=
    (fiveRootSubgroup_le_unipotent _ _).trans (le_trans le_sup_left le_sup_left)
  rw [parabolic₁_pCoreIn, Subgroup.map_subgroupOf_eq_of_le hle]

/-- The full short parabolic has characteristic two intrinsically. -/
public theorem parabolic₁_centralizer_pCore [Finite F] :
    Subgroup.centralizer
        (pCore 2 (parabolic₁ (F := F)) : Set (parabolic₁ (F := F))) ≤
      pCore 2 (parabolic₁ (F := F)) := by
  rw [parabolic₁_pCore]
  exact short_radical_selfCentralizing

end Atlas.G2.EvenLocal
