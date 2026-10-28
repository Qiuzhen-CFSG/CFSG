module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.GlobalGeometry.OddCoreUpgrade
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.GlobalGeometry.NormalizerEligibility
public import Theory.SpecificGroups.SL2.CardFourEquiv
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# Constructing the graph-centralizer component

The intrinsic model of O²(C_L(τ)) gives a simple perfect group of order sixty.
Normality of L in I makes this residual normal in C_I(τ). The representative
centralizer bound identifies its further centralizer at v with the global
one. Thus the residual is a genuine local 2-component, to which I.3.1 applies.
The odd-core bound and centralization proved in `OddCoreUpgrade` discharge
the ordinary-component premise in I.3.1(2).

Only the intrinsic residual isomorphism and O(C_I(τf)) ≃ E₉ are model inputs.
In particular local or global component existence is not a model input.
Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
proof of 15.3.38, printed pp.1136--1137, using I.3.1(2), p.414.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.GlobalGeometry
universe u
variable {G : Type u} [Group G]

/-- The actual intrinsic two-residual of C_L(τ), embedded in C_G(τ). -/
noncomputable def graphResidualIn (L : Subgroup G) (τ : G) :
    Subgroup (centralizer ({τ} : Set G)) :=
  (pResidual 2 (L.subgroupOf (centralizer ({τ} : Set G)))).map
    (L.subgroupOf (centralizer ({τ} : Set G))).subtype

private theorem psl_four_properties {B : Type*} [Group B] [Finite B]
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 4)
    (e : B ≃* PSL(2,F)) : IsQuasisimple B ∧ pPrimeCore 2 B = ⊥ := by
  obtain ⟨ea⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup B := (MulEquiv.isSimpleGroup_congr (e.trans ea)).mpr inferInstance
  let : Group.IsPerfect PSL(2,F) :=
    GorensteinWalter.psl2_isPerfect_of_card_gt_three F (by omega)
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective
    (f := e.symm.toMonoidHom) e.symm.surjective
  have hc : center B = ⊥ := by
    rcases (inferInstance : (center B).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exact (Group.IsPerfect.not_isMulCommutative B (center_eq_top_iff.mp h)).elim
  have hquasi : IsQuasisimple B := {
    simple := (MulEquiv.isSimpleGroup_congr
      ((QuotientGroup.quotientMulEquivOfEq hc).trans (QuotientGroup.quotientBot (G := B)))).mpr
        inferInstance }
  refine ⟨hquasi, ?_⟩
  rcases (inferInstance : (pPrimeCore 2 B).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · have hcard : Nat.card B = 60 := by
      rw [Nat.card_congr (e.trans ea).toEquiv, nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    have hp := pPrimeCore_coprime_card (p := 2) (G := B)
    rw [h, Nat.card_congr (topEquiv : (⊤ : Subgroup B) ≃* B).toEquiv, hcard] at hp
    norm_num at hp

private theorem local_twoComponent_of_normal_psl_four [Finite G]
    (B D : Subgroup G) (hBD : B ≤ D) (hDB : D ≤ normalizer (B : Set G))
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 4)
    (e : B ≃* PSL(2,F)) : IsTwoComponent (B.subgroupOf D) := by
  let J := B.subgroupOf D
  let ej : J ≃* B := subgroupOfEquivOfLe hBD
  obtain ⟨hq, ho⟩ := psl_four_properties hF (ej.trans e)
  let : J.Normal := normal_subgroupOf_of_le_normalizer hDB
  have hj : IsComponent D J := ⟨(inferInstance : J.Normal).isSubnormal, hq⟩
  refine ⟨component_isCComponent hj, ?_⟩
  let : IsQuasisimple J := hq
  exact IsQuasisimple.of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq ho).trans (QuotientGroup.quotientBot (G := J))).symm

/-- A nonidentity element of a nonabelian simple group has a proper
centralizer, so the standing proper-K hypothesis applies to that centralizer. -/
theorem centralizer_isKGroup [Finite G] {κ : GroupClass.{u}}
    (hG : IsSimpleQTKE κ G) {τ : G} (hτ : τ ≠ 1) :
    IsKGroup κ (centralizer ({τ} : Set G)) := by
  let : IsSimpleGroup G := hG.simple
  apply hG.properK
  intro he
  have hcenter : center G = ⊥ := by
    rcases (inferInstance : (center G).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exact (hG.nonabelian (center_eq_top_iff.mp h)).elim
  have hτc : τ ∈ center G := mem_center_iff.mpr (fun g =>
    mem_centralizer_singleton_iff.mp (he ▸ (mem_top g)))
  exact hτ (mem_bot.mp (hcenter ▸ hτc))

/-- Construct an ordinary component of the graph involution centralizer.
The local model uses the same coefficient field as the marked cover. -/
theorem exists_graph_component [Finite G] {κ : GroupClass.{u}}
    (hG : IsSimpleQTKE κ G) (balance : EarlierBalance κ)
    (T : Sylow 2 G) (Y S L V I J : Subgroup G) [IsKleinFour V]
    (c : ProjectiveMarking L 4) (d : SylowThreeLift T Y S L c)
    (hI : I = normalizer (V : Set G)) (hLI : L ≤ I)
    (hIL : I ≤ normalizer (L : Set G))
    (hZ : (center L).map L.subtype = V)
    (v : G) (hv : v ∈ V) (hv1 : v ≠ 1) (hv2 : orderOf v = 2)
    (hSCv : S ≤ centralizer ({v} : Set G))
    (hCv : centralizer ({v} : Set G) ≤ I) (hJI : J ≤ I)
    (htrans : ∀ x y : G, x ∈ V → x ≠ 1 → y ∈ V → y ≠ 1 →
      ∃ m : J, (MulAut.conj (m : G)) x = y)
    (hfixed : (d.dihedral.firstReflection : G) * (d.dihedral.halfTurn : G) ∈
      centralizer (V : Set G))
    (emodel : pPrimeCore 2 ↥(I ⊓ centralizer
      ({(d.dihedral.firstReflection : G) * (d.dihedral.halfTurn : G)} : Set G)) ≃*
        Multiplicative (Fin 2 → ZMod 3))
    (graphModel : graphResidualIn L (d.dihedral.firstReflection : G) ≃* PSL(2,c.F)) :
    ∃ K : Subgroup (centralizer ({(d.dihedral.firstReflection : G)} : Set G)),
      IsComponent (centralizer ({(d.dihedral.firstReflection : G)} : Set G)) K := by
  let τ : G := d.dihedral.firstReflection
  let H := centralizer ({τ} : Set G)
  let D := I.subgroupOf H
  let A := L.subgroupOf H
  let B := graphResidualIn L τ
  have hvH : v ∈ H := mem_centralizer_singleton_iff.mpr
    (mem_centralizer_singleton_iff.mp (hSCv d.first_mem)).symm
  let vH : H := ⟨v, hvH⟩
  let P := zpowers vH
  have hP : IsPGroup 2 P := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, ← Subgroup.orderOf_coe, hv2, pow_one])
  have hCD : centralizer (P : Set H) ≤ D := by
    intro x hx
    apply hCv
    apply mem_centralizer_singleton_iff.mpr
    exact (congrArg Subtype.val (hx vH (mem_zpowers vH))).symm
  have hDA : D ≤ normalizer (A : Set H) := by
    intro x hx
    apply mem_normalizer_iff.mpr
    intro y
    exact mem_normalizer_iff.mp (hIL hx) y
  have hDB : D ≤ normalizer (B : Set H) :=
    hDA.trans (normalizer_le_normalizer_characteristic_image A (pResidual 2 A))
  have hBA : B ≤ A := map_subtype_le _
  have hBD : B ≤ D := hBA.trans (comap_mono hLI)
  have hBC : B ≤ centralizer (P : Set H) := by
    change B ≤ centralizer (zpowers vH : Set H)
    rw [zpowers_eq_closure, centralizer_closure]
    intro x hx
    apply mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    obtain ⟨w, hw, hwv⟩ := mem_map.mp (hZ.symm ▸ hv)
    have he := congrArg Subtype.val (mem_center_iff.mp hw ⟨x, hBA hx⟩)
    change (w : G) = v at hwv
    change (x : G) * (w : G) = (w : G) * (x : G) at he
    change (x : G) * v = v * (x : G)
    rwa [hwv] at he
  have hlocal : IsTwoComponent (B.subgroupOf (D ⊓ centralizer (P : Set H))) :=
    local_twoComponent_of_normal_psl_four B _ (le_inf hBD hBC)
      (inf_le_left.trans hDB) c.card graphModel
  have hτ1 : τ ≠ 1 := by
    intro he
    have hτT : d.dihedral.firstReflection = 1 := Subtype.ext he
    have ho := d.dihedral.firstReflection_order
    rw [hτT, orderOf_one] at ho
    omega
  have hodd := (graph_oddCore_card_dvd_nine T Y S L V I J c d hI v hv hv1 hCv
    hJI htrans hfixed emodel).2
  exact exists_component_of_local_twoComponent balance (centralizer_isKGroup hG hτ1)
    P D B hP hCD hlocal hodd

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.GlobalGeometry
