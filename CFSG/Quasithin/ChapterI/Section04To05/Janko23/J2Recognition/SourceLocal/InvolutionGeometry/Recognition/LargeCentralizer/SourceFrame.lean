module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.Contracts
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame.Contracts
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame.CubicConstruction
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame.OutsideSizes
public import Theory.GroupTheory.FusedSubgroupCentralizerSylow
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.PGroup.ExtraspecialAbelianIndexTwo

/-!
# Assembly of the marked §46 frame

The source cubic geometry and the separate outside-centralizer calculation
give the exact core and double-centralizer intersections. The elementary
join has order sixteen and cannot lie in the extraspecial core of order
thirty-two, so its four-group complement contains an outside involution.
Local fusion marks the conjugates of z in the join. The normalizer condition
then promotes the join to a genuine Sylow subgroup of the full C_G(t).

The final existence theorem discharges both earlier source constructions:
`CubicConstruction` constructs the geometry on the canonical root product,
and `OutsideSizes` calculates the two centralizer orders inside H. Thus only
the seed and supplied local census remain as inputs; the order and recognition
of the full second-involution centralizer are subsequent source obligations.

Source: Aschbacher, *Sporadic Groups* (1994), 46.3, 46.14 and the beginning
of 47.1, printed pp.251,257–260.
-/

@[expose] public section
open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame

variable {G : Type*} [Group G] [Finite G]

namespace CubicGeometry
variable {D : Seed G} {P : ReturningPair D} (C : CubicGeometry P)

theorem join_commute {a b : G} (ha : a ∈ P.E ⊔ C.U) (hb : b ∈ P.E ⊔ C.U) :
    Commute a b := by
  let : IsElementaryAbelian 2 (P.E ⊔ C.U : Subgroup G) := C.elementary
  exact congrArg Subtype.val
    ((IsMulCommutative.is_comm (M := (P.E ⊔ C.U : Subgroup G))).comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem join_card : Nat.card (P.E ⊔ C.U : Subgroup G) = 16 := by
  have hn : C.U ≤ normalizer (P.E : Set G) := by
    apply le_trans _ (Subgroup.centralizer_le_normalizer _)
    intro u hu e he
    exact (C.join_commute (mem_sup_left he) (mem_sup_right hu)).eq
  rw [card_sup_eq_mul_of_normalizes_of_disjoint _ _ hn C.disjoint, P.E_card, C.U_card]

theorem join_not_le_core : ¬ P.E ⊔ C.U ≤ ambientCore D.z := by
  intro hle
  let Q := ambientCore D.z
  let A := P.E ⊔ C.U
  let : IsExtraspecial 2 Q := D.localType.ambientCore_isExtraspecial
  let : IsElementaryAbelian 2 A := C.elementary
  let : IsElementaryAbelian 2 (A.subgroupOf Q) := IsElementaryAbelian.subgroupOf hle
  have hcard : Nat.card (A.subgroupOf Q) = 16 :=
    (Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv).trans C.join_card
  have hi : (A.subgroupOf Q).index = 2 := by
    have hh := (A.subgroupOf Q).card_mul_index
    rw [hcard, D.localType.ambientCore_card] at hh
    omega
  have hZ : center Q ≤ A.subgroupOf Q := by
    intro q hq
    have hline : (q : G) ∈ zpowers D.z :=
      D.localType.core_center_image ▸ mem_map_of_mem Q.subtype hq
    exact mem_sup_left ((zpowers_le.mpr P.z_mem_E) hline)
  exact IsExtraspecial.not_isMulCommutative_of_index_two
    (by rw [D.localType.ambientCore_card]; decide) (A.subgroupOf Q) hi hZ inferInstance

/-- The geometry itself supplies an outside involution, without recognition. -/
theorem exists_outside : ∃ t ∈ C.U, orderOf t = 2 ∧ t ∉ ambientCore D.z := by
  classical
  have hn : ¬ C.U ≤ ambientCore D.z := fun hu =>
    C.join_not_le_core (sup_le P.E_le_core hu)
  obtain ⟨t, htU, htQ⟩ := SetLike.not_le_iff_exists.mp hn
  have ht1 : t ≠ 1 := fun hh => htQ (hh ▸ (ambientCore D.z).one_mem)
  let : IsElementaryAbelian 2 (P.E ⊔ C.U : Subgroup G) := C.elementary
  exact ⟨t, htU, orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (A := P.E ⊔ C.U) t (mem_sup_right htU)) ht1, htQ⟩

theorem join_le_source_centralizer : P.E ⊔ C.U ≤ involutionCentralizer D.z :=
  C.join_le_R.trans (P.R_le_double_centralizer.trans inf_le_left)

theorem join_le_centralizer {t : G} (ht : t ∈ C.U) :
    P.E ⊔ C.U ≤ involutionCentralizer t := by
  intro a ha
  exact mem_centralizer_singleton_iff.mpr (C.join_commute ha (mem_sup_right ht)).eq

theorem X1_le_centralizer {t : G} (ht : t ∈ C.U) : C.X1 ≤ involutionCentralizer t := by
  have hc : t ∈ centralizer (C.X1 : Set G) := (C.U_eq.symm ▸ ht).2
  intro x hx
  exact mem_centralizer_singleton_iff.mpr (hc x hx)

/-- The source fixed-point orders identify both literal ambient intersections. -/
theorem intersections (hsizes : OutsideCentralizerSizes D) {t : G}
    (ht : t ∈ C.U) (ht2 : orderOf t = 2) (htQ : t ∉ ambientCore D.z) :
    (P.E ⊔ C.U) ⊓ ambientCore D.z = P.E ∧
    involutionCentralizer t ⊓ involutionCentralizer D.z = P.E ⊔ C.U := by
  obtain ⟨hQ, hH⟩ := hsizes t (C.join_le_source_centralizer (mem_sup_right ht)) ht2 htQ
  have hE : P.E = involutionCentralizer t ⊓ ambientCore D.z :=
    eq_of_le_of_card_ge (le_inf (le_sup_left.trans (C.join_le_centralizer ht)) P.E_le_core)
      (by rw [hQ, P.E_card])
  constructor
  · apply le_antisymm
    · exact (inf_le_inf (C.join_le_centralizer ht) le_rfl).trans hE.symm.le
    · exact le_inf le_sup_left P.E_le_core
  · exact (eq_of_le_of_card_ge
      (le_inf (C.join_le_centralizer ht) C.join_le_source_centralizer)
      (by rw [hH, C.join_card])).symm

private theorem centralizer_le_join {t : G} (ht : t ∈ C.U)
    (hdouble : involutionCentralizer t ⊓ involutionCentralizer D.z = P.E ⊔ C.U)
    {e : G} (he : e ∈ P.E) (hne : e ≠ 1) :
    involutionCentralizer t ⊓ involutionCentralizer e ≤ P.E ⊔ C.U := by
  obtain ⟨x, hx⟩ := C.X1_transitive e he hne D.z P.z_mem_E
    (orderOf_eq_prime_iff.mp D.localType.involution).2
  let f := MulAut.conj (x : G)
  have hf : f e = D.z := hx
  have hxK := C.X1_le_centralizer ht x.property
  have hmap : (involutionCentralizer t ⊓ involutionCentralizer e).map f.toMonoidHom ≤
      involutionCentralizer t ⊓ involutionCentralizer D.z := by
    rintro _ ⟨a, ha, rfl⟩
    refine ⟨(involutionCentralizer t).mul_mem
      ((involutionCentralizer t).mul_mem hxK ha.1)
      ((involutionCentralizer t).inv_mem hxK), ?_⟩
    apply mem_centralizer_singleton_iff.mpr
    change f a * D.z = D.z * f a
    have hh := congrArg f (mem_centralizer_singleton_iff.mp ha.2)
    simpa only [map_mul, hf] using hh
  have hcard := card_le_of_le hmap
  rw [card_map_of_injective f.injective, hdouble] at hcard
  have hle : P.E ⊔ C.U ≤ involutionCentralizer t ⊓ involutionCentralizer e := by
    apply le_inf (C.join_le_centralizer ht)
    intro a ha
    exact mem_centralizer_singleton_iff.mpr (C.join_commute ha (mem_sup_left he)).eq
  exact (eq_of_le_of_card_ge hle hcard).symm.le

/-- Actual application of the normalizer-condition argument to the marked
join and the literal involution centralizer. -/
theorem exists_sylow (L : LocalCensus D) {t : G} (ht : t ∈ C.U)
    (hcore : (P.E ⊔ C.U) ⊓ ambientCore D.z = P.E)
    (hdouble : involutionCentralizer t ⊓ involutionCentralizer D.z = P.E ⊔ C.U) :
    ∃ A : Sylow 2 (involutionCentralizer t),
      (A : Subgroup (involutionCentralizer t)).map (involutionCentralizer t).subtype =
        P.E ⊔ C.U := by
  let : IsElementaryAbelian 2 (P.E ⊔ C.U : Subgroup G) := C.elementary
  apply exists_sylow_of_fused_subgroup _ _ P.E D.z
    (IsElementaryAbelian.isPGroup 2 _) (C.join_le_centralizer ht) le_sup_left
  · intro he
    have hh := P.E_card
    rw [he, card_bot] at hh
    omega
  · intro e he hne
    have ho : orderOf e = 2 := orderOf_eq_prime
      (elemPow_eq_one_of_isElementaryAbelian (A := P.E ⊔ C.U) e he) hne
    rw [L.core_fusion e (C.join_le_source_centralizer he) ho]
    exact ⟨fun hq => hcore ▸ (show e ∈ (P.E ⊔ C.U) ⊓ ambientCore D.z from ⟨he, hq⟩),
      fun heE => P.E_le_core heE⟩
  · exact fun e he hne => C.centralizer_le_join ht hdouble he hne

end CubicGeometry

/-- Conditional assembly. Both earlier-source inputs must be constructed
before this establishes the requested frame existence theorem. -/
theorem exists_localFrame_of_source_geometry (D : Seed G) (L : LocalCensus D)
    (hsizes : OutsideCentralizerSizes D)
    (hgeometry : ∃ P : ReturningPair D, Nonempty (CubicGeometry P)) :
    ∃ t : G, OtherInvolution D t ∧ Nonempty (LocalFrame D t) := by
  obtain ⟨P, ⟨C⟩⟩ := hgeometry
  obtain ⟨t, htU, ht2, htQ⟩ := C.exists_outside
  have ht1 := (orderOf_eq_prime_iff.mp ht2).2
  have htH := C.join_le_source_centralizer (mem_sup_right htU)
  have hother : OtherInvolution D t := ⟨ht2, fun hh => htQ ((L.core_fusion t htH ht2).mp hh)⟩
  obtain ⟨hcore, hdouble⟩ := C.intersections hsizes htU ht2 htQ
  obtain ⟨A, hA⟩ := C.exists_sylow L htU hcore hdouble
  refine ⟨t, hother, ⟨{
    R := P.R, E := P.E, U := C.U, X1 := C.X1, X3 := C.X3
    R_card := C.R_card, E_center := C.E_center, E_card := P.E_card
    U_card := C.U_card, disjoint := C.disjoint, elementary := C.elementary
    join_le_R := C.join_le_R, U_eq := C.U_eq, z_mem := P.z_mem_E, t_mem := htU
    A := A, A_eq := hA, core_intersection := hcore, double_centralizer := hdouble
    X1_card := C.X1_card, X1_le := C.X1_le_centralizer htU
    X1_normalizes := C.X1_normalizes, X1_transitive := C.X1_transitive
    X3_card := C.X3_card, X3_normalizes := C.X3_normalizes
    X3_centralizes := C.X3_centralizes, X3_transitive := C.X3_transitive
    normalizer_intersection_card := C.normalizer_intersection_card t htU ht1
  }⟩⟩

/-- The marked §46 frame for a representative of the second involution class.
The canonical root-product geometry and the local centralizer orders discharge
both earlier-source inputs to the assembly. -/
theorem exists_localFrame (D : Seed G) (L : LocalCensus D) :
    ∃ t : G, OtherInvolution D t ∧ Nonempty (LocalFrame D t) :=
  exists_localFrame_of_source_geometry D L (outsideCentralizerSizes D)
    (exists_cubicGeometry D L)

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame
