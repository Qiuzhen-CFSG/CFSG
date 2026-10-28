module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeSylow
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalLocalRightGeometry
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeAssembly

/-!
# Right-family geometry before Cartan normalization

The original odd Hall subgroup B lies in the residual and normalizes its
Sylow subgroup. Its orbit on the source family has odd cardinality at most
two, so B fixes every selected factor. The same orbit calculation for T
bounds the index of N_T(R). Hall restriction then identifies the literal
right Borel without assuming that the left Cartan normalizes the residual.

Together with the selected factor's relative C-component property these
facts construct every field of `Prime.RightData`, and hence the genuine
F.1.1 pair (DS,R) when its generated two-core vanishes. In the other branch,
the family has exactly two members and D moves R, with N_T(R) of index two.

The source family and relative component selection remain explicit. The
shared family construction belongs to qt-d-1222-rankone-generic-global;
its use here and the remaining zero-core and changed-Sylow classification
belong to qt-d-1222-rankone-cartan-local-to-global. This is a conditional
geometric reduction, not the final normalization theorem.

Source: Aschbacher--Smith, 5.1.10--11, the selection before 5.2.1, and
5.2.2, printed pp.634--635,646--648 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]

private theorem family_normalizer_index {U R : Subgroup G} {ℛ : Set (Subgroup G)}
    (hR : R ∈ ℛ)
    (hi : ∀ u : U, ∀ Q ∈ ℛ, Q.map (MulAut.conj (u : G)).toMonoidHom ∈ ℛ) :
    (U ⊓ normalizer (R : Set G)).relIndex U ≤ ℛ.ncard := by
  let : MulAction U (Subgroup G) :=
    MulAction.compHom (Subgroup G) ((MulAut.conj : G →* MulAut G).comp U.subtype)
  have he : (U ⊓ normalizer (R : Set G)).subgroupOf U = MulAction.stabilizer U R := by
    ext u
    constructor
    · intro hu
      exact mem_normalizer_iff_map_conj_eq.mp hu.2
    · intro hu
      exact ⟨u.property, mem_normalizer_iff_map_conj_eq.mpr hu⟩
  change ((U ⊓ normalizer (R : Set G)).subgroupOf U).index ≤ _
  rw [he, MulAction.index_stabilizer]
  exact Set.ncard_le_ncard (by
    rintro Q ⟨u, rfl⟩
    exact hi u R hR)

variable {T : Sylow 2 G} {L H R : Subgroup G} {ℛ : Set (Subgroup G)}

/-- The original right Hall subgroup fixes each source factor before any left-Cartan normalization. -/
theorem RightGeometry.right_cartan_normalizes {A B : Subgroup G}
    (d : RightGeometry T L H ℛ) (c : CartanPair T L H A B)
    (hR : R ∈ ℛ) : B ≤ normalizer (R : Set G) := by
  have hBTK := (le_inf (c.right_le.trans inf_le_left) (right_cartan_le_residual c)).trans
    d.two_closed
  have hb := (family_normalizer_index hR (fun b Q hQ => d.invariant b
    ((c.right_le.trans inf_le_right).trans (le_normalizer_residual H) b.property)
    (hBTK b.property) Q hQ)).trans d.small
  have ho : Odd (Nat.card B) := by
    rw [← Nat.card_congr (subgroupOfEquivOfLe c.right_le).toEquiv]
    exact OddHall.odd_hall_odd c.right_hall
  have hi : Odd ((B ⊓ normalizer (R : Set G)).relIndex B) :=
    ho.of_dvd_nat ((B ⊓ normalizer (R : Set G)).subgroupOf B).index_dvd_card
  have hp : (B ⊓ normalizer (R : Set G)).relIndex B ≠ 0 :=
    ((B ⊓ normalizer (R : Set G)).subgroupOf B).index_ne_zero_of_finite
  have hone : (B ⊓ normalizer (R : Set G)).relIndex B = 1 := by
    have hn := hi.not_two_dvd_nat
    omega
  exact (relIndex_eq_one.mp hone).trans inf_le_right

/-- The at-most-two-member source family bounds the actual relative normalizer index. -/
theorem RightGeometry.normalizingSylow_index_le_two
    (d : RightGeometry T L H ℛ) (hTH : (T : Subgroup G) ≤ H)
    (hR : R ∈ ℛ) : (Prime.normalizingSylow T R).relIndex (T : Subgroup G) ≤ 2 := by
  have hTK := hTH.trans (le_normalizer_residual H)
  have hTTK : (T : Subgroup G) ≤
      normalizer (((T : Subgroup G) ⊓ residual H : Subgroup G) : Set G) :=
    (le_inf (T : Subgroup G).le_normalizer hTK).trans inf_normalizer_le_normalizer_inf
  exact (family_normalizer_index hR (fun t Q hQ =>
    d.invariant t (hTK t.property) (hTTK t.property) Q hQ)).trans d.small

/-- The source Sylow intersection and the original Hall B give the literal right Borel. -/
theorem RightGeometry.prime_borel {A B : Subgroup G}
    (d : RightGeometry T L H ℛ) (c : CartanPair T L H A B)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hTH : (T : Subgroup G) ≤ H) (hR : R ∈ ℛ) :
    ChapterF.Source.borel R (sourceS L H) = (sourceS L H ⊓ R) ⊔ (B ⊓ R) := by
  have hBN := d.right_cartan_normalizes c hR
  have hSR := d.sourceS_intersection hTL hTH hR
  have hb : ChapterF.Source.borel R (sourceS L H) = normalizer (L : Set G) ⊓ R := by
    unfold ChapterF.Source.borel
    rw [hSR]
    exact d.overlap R hR
  let U := normalizer (L : Set G) ⊓ R
  have hRH : R ≤ H := (d.le_residual R hR).trans (map_subtype_le _)
  have hU : U ≤ intersection L H := le_inf inf_le_left (inf_le_right.trans hRH)
  have hBU : B ≤ normalizer (U : Set G) :=
    (le_inf ((c.right_le.trans inf_le_left).trans (normalizer (L : Set G)).le_normalizer)
      hBN).trans inf_normalizer_le_normalizer_inf
  have hh := OddHall.hall_restrict_of_normalizes c.right_hall c.right_le hU hBU
  obtain ⟨P,hP⟩ := d.sylow R hR
  obtain ⟨Q,hQ⟩ := P.exists_map_subtype_eq_of_le (show U ≤ R from inf_le_right)
    (hP ▸ le_inf (inf_le_left.trans hTL) inf_le_right)
  have he := congrArg (Subgroup.map U.subtype) (OddHall.sylow_complement_of_hall Q hh).sup_eq_top
  have hi : B ⊓ U = B ⊓ R := by
    dsimp [U]
    rw [← inf_assoc, inf_eq_left.mpr (c.right_le.trans inf_le_left)]
  rw [Subgroup.map_sup, hQ, hP, subgroupOf_map_subtype, hi,
    ← MonoidHom.range_eq_map, range_subtype] at he
  rw [hb, hSR]
  exact he.symm

/-- Construct every right-side prime-pair clause from the selected source geometry and relative component. -/
theorem RightGeometry.primeRightData {A B : Subgroup G}
    (d : RightGeometry T L H ℛ) (c : CartanPair T L H A B)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hR : R ∈ ℛ)
    (hC : (R.subgroupOf (R ⊔ Prime.normalizingSylow T R)).IsCComponent) :
    Prime.RightData T L H B R := by
  refine ⟨d.le_residual R hR, ?_, d.generates R hR, ?_, hC,
    d.normalizingSylow_index_le_two hH.1.1.2 hR,
    d.sourceS_intersection_residual hTL hH.1.1.2, d.S_normalizes R hR,
    d.right_cartan_normalizes c hR, ?_, d.quotient R hR,
    d.prime_borel c hTL hH.1.1.2 hR⟩
  · intro hRM
    exact hH.1.2 ((d.generates R hR) ▸ sup_le hRM hTL)
  · intro hs
    let := hs
    exact hC.not_isSolvable
      (Group.isSolvable_of_isSolvable_injective
        (f := (subgroupOfEquivOfLe
          (show R ≤ R ⊔ Prime.normalizingSylow T R from le_sup_left)).toMonoidHom)
        (subgroupOfEquivOfLe le_sup_left).injective)
  · rw [d.sourceS_intersection hTL hH.1.1.2 hR]
    exact d.sylow R hR

/-- An original C-component restricts to the required relative C-component, covering the Bender selection. -/
theorem RightGeometry.primeRightData_of_component {A B : Subgroup G}
    (d : RightGeometry T L H ℛ) (c : CartanPair T L H A B)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hR : R ∈ ℛ) (hC : (R.subgroupOf H).IsCComponent) :
    Prime.RightData T L H B R :=
  d.primeRightData c hTL hH hR (hC.subgroupOf_of_le le_sup_left
    (sup_le ((d.le_residual R hR).trans (map_subtype_le _))
      (inf_le_left.trans hH.1.1.2)))

/-- Apply the entire geometric construction to genuine F.1.1 on the literal pair (DS,R). -/
theorem RightGeometry.prime_hypothesisF11 {W A B D : Subgroup G} {n p : ℕ}
    (d : RightGeometry T L H ℛ) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hR : R ∈ ℛ)
    (hC : (R.subgroupOf (R ⊔ Prime.normalizingSylow T R)).IsCComponent)
    (hz : (Prime.generated L H D R).pCoreIn 2 = ⊥) :
    ChapterF.Source.HypothesisF11 ![D ⊔ sourceS L H, R] (sourceS L H) :=
  (d.primeRightData c h.sylow_normalizes hH hR hC).hypothesisF11 h hH c hd hz

/-- Nonzero generated core forces exactly two source factors, via the strict Sylow normalizer. -/
theorem RightGeometry.prime_nonzero_core_family_card {W A B D : Subgroup G} {n p : ℕ}
    (d : RightGeometry T L H ℛ) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hR : R ∈ ℛ)
    (hC : (R.subgroupOf (R ⊔ Prime.normalizingSylow T R)).IsCComponent)
    (hz : (Prime.generated L H D R).pCoreIn 2 ≠ ⊥) : ℛ.ncard = 2 := by
  have hTK := hH.1.1.2.trans (le_normalizer_residual H)
  have hTTK : (T : Subgroup G) ≤
      normalizer (((T : Subgroup G) ⊓ residual H : Subgroup G) : Set G) :=
    (le_inf (T : Subgroup G).le_normalizer hTK).trans inf_normalizer_le_normalizer_inf
  have hi := family_normalizer_index hR (fun t Q hQ =>
    d.invariant t (hTK t.property) (hTTK t.property) Q hQ)
  let e := (d.primeRightData c h.sylow_normalizes hH hR hC).localData h hH c hd
  have he := e.normalizingSylow_index hH.1.1.2 c hd hz
  change (Prime.normalizingSylow T R).relIndex (T : Subgroup G) ≤ ℛ.ncard at hi
  rw [he] at hi
  exact le_antisymm d.small hi

/-- The source family gives either the genuine zero-core amalgam or the index-two moving-factor branch. -/
theorem RightGeometry.prime_pair_dichotomy {W A B D : Subgroup G} {n p : ℕ}
    (d : RightGeometry T L H ℛ) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hR : R ∈ ℛ)
    (hC : (R.subgroupOf (R ⊔ Prime.normalizingSylow T R)).IsCComponent) :
    ChapterF.Source.HypothesisF11 ![D ⊔ sourceS L H, R] (sourceS L H) ∨
      ((Prime.generated L H D R).pCoreIn 2 ≠ ⊥ ∧
        ℛ.ncard = 2 ∧ ¬ D ≤ normalizer (R : Set G) ∧
        (Prime.normalizingSylow T R).relIndex (T : Subgroup G) = 2) := by
  by_cases hz : (Prime.generated L H D R).pCoreIn 2 = ⊥
  · exact Or.inl (d.prime_hypothesisF11 h hH c hd hR hC hz)
  · let e := (d.primeRightData c h.sylow_normalizes hH hR hC).localData h hH c hd
    exact Or.inr ⟨hz, d.prime_nonzero_core_family_card h hH c hd hR hC hz,
      e.prime_actor_not_normalizes_right h hH c hd hz,
      e.normalizingSylow_index hH.1.1.2 c hd hz⟩

/-- The nontrivial Sylow coset gives exactly the second source factor and generates the residual with R. -/
theorem RightGeometry.prime_nonzero_core_two_factors {W A B D : Subgroup G} {n p : ℕ}
    (d : RightGeometry T L H ℛ) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hR : R ∈ ℛ)
    (hC : (R.subgroupOf (R ⊔ Prime.normalizingSylow T R)).IsCComponent)
    (hz : (Prime.generated L H D R).pCoreIn 2 ≠ ⊥) :
    ∃ t ∈ (T : Subgroup G), t ∉ Prime.normalizingSylow T R ∧
      ℛ = {R, R.map (MulAut.conj t).toMonoidHom} ∧
      residual H = R ⊔ R.map (MulAut.conj t).toMonoidHom := by
  let e := (d.primeRightData c h.sylow_normalizes hH hR hC).localData h hH c hd
  obtain ⟨t, ht, ht0⟩ := SetLike.exists_of_lt (e.normalizingSylow_lt hH.1.1.2 c hd hz)
  have hTK := hH.1.1.2.trans (le_normalizer_residual H)
  have hTTK : (T : Subgroup G) ≤
      normalizer (((T : Subgroup G) ⊓ residual H : Subgroup G) : Set G) :=
    (le_inf (T : Subgroup G).le_normalizer hTK).trans inf_normalizer_le_normalizer_inf
  have hRt := d.invariant t (hTK ht) (hTTK ht) R hR
  have hne : R ≠ R.map (MulAut.conj t).toMonoidHom := by
    intro he
    exact ht0 ⟨ht, mem_normalizer_iff_map_conj_eq.mpr he.symm⟩
  have hpair : ({R, R.map (MulAut.conj t).toMonoidHom} : Set (Subgroup G)) ⊆ ℛ :=
    Set.insert_subset hR (Set.singleton_subset_iff.mpr hRt)
  refine ⟨t, ht, ht0, ?_, e.residual_eq_two_conjugates hH.1.1.2 c hd hz ht ht0⟩
  exact (Set.eq_of_subset_of_ncard_le hpair
    ((Set.ncard_pair hne).symm ▸ d.small)).symm

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]

/-- The earlier source family and relative component selection discharge the
entire `SourceLocalConstruction` contract. Family selection remains explicit;
the right Cartan, Borel, index and all left-side clauses are constructed. -/
theorem sourceLocalConstruction_of_right_families
    (hfamily : ∀ (T : Sylow 2 G) (L W : Subgroup G) (n : ℕ),
      Input KnownSimple.IsKnownSimple T L W n →
      ∀ H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
        1 < ChapterE.generationParameter H →
        ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4 →
        ∃ ℛ : Set (Subgroup G), Global.RightGeometry T L H ℛ ∧
          ∃ R ∈ ℛ, (R.subgroupOf (R ⊔ normalizingSylow T R)).IsCComponent) :
    SourceLocalConstruction G := by
  intro T L W n h H hH hgen hthree A B c _ _ p D hd
  obtain ⟨ℛ, d, R, hR, hC⟩ := hfamily T L W n h H hH hgen hthree
  exact ⟨R, (d.primeRightData c h.sylow_normalizes hH hR hC).localData h hH c hd⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
