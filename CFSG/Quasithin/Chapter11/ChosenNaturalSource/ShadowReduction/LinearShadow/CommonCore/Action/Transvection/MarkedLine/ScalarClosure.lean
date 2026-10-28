module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.Transvection.MarkedLine.Coordinates

/-!
# Scalar closure of the original marked subgroup

The equation U=[U,B] implies that B normalizes U. In compatible natural
coordinates, both a vector of U and its B-conjugate lie in the upper fixed
space. The matrix equation therefore makes conjugation multiplication by
the upper-left entry, simultaneously on all natural summands. If these
actual entries span the field additively, U is closed under every scalar.
Its source order q then gives field dimension one.

The scalar-span premise is explicit: neither a single nonidentity scalar
nor the order of U proves it. Source: Aschbacher--Smith 11.3.7(4), p.773.
-/

@[expose] public noncomputable section
open Subgroup Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
open CFSG.Quasithin.ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] {T : Sylow 2 G} {H A : Subgroup G} {F : BinaryField}

/-- Scalars of the actual embedded Cartan actors after the retained basis change. -/
def cartanScalarSet (c : NaturalQuotientMarking T H F) (b : SL(2,F.Carrier))
    (B : Subgroup G) : Set F.Carrier :=
  {a | ∃ k : outsideResidual H, (k : G) ∈ B ∧
    (b * c.quotientEquiv (QuotientGroup.mk' _ k) * b⁻¹).val 0 0 = a}

/-- The model O³(Fqˣ) Ω₁(O₃(Fqˣ)); the omega factor is taken at three. -/
def torusCartanPart (F : BinaryField) : Subgroup F.Carrierˣ :=
  (pResidual 3 F.Carrierˣ) ⊔
    (omega₁ (pCore 3 F.Carrierˣ) (p := 3)).map (pCore 3 F.Carrierˣ).subtype

/-- The actual coefficients of the model odd Cartan part. -/
def torusScalarSet (F : BinaryField) : Set F.Carrier :=
  Set.range (fun a : torusCartanPart F => (a.val : F.Carrier))

namespace NaturalSylowCoordinates
variable {m : ℕ} (n : NaturalSylowCoordinates T H A F m)

/-- The additive image of the literal subgroup, before establishing scalar closure. -/
def subgroupImage (U : Subgroup G) : AddSubgroup (Fin m → Fin 2 → F.Carrier) :=
  ((U.subgroupOf (omegaClosure T H)).map n.coordinates.toMonoidHom).toAddSubgroup

theorem mem_subgroupImage (U : Subgroup G) (v : omegaClosure T H) :
    (n.coordinates v).toAdd ∈ n.subgroupImage U ↔ (v : G) ∈ U := by
  change n.coordinates v ∈ (U.subgroupOf (omegaClosure T H)).map n.coordinates.toMonoidHom ↔ _
  constructor
  · rintro ⟨w,hw,he⟩
    exact n.coordinates.injective he ▸ hw
  · exact fun hv => mem_map_of_mem _ hv

/-- Additive closure of scalar operators preserves an additive subgroup. -/
theorem smul_mem_of_scalar_span (U : AddSubgroup (Fin m → Fin 2 → F.Carrier))
    (s : Set F.Carrier) (hs : AddSubgroup.closure s = ⊤)
    (hstable : ∀ a ∈ s, ∀ v ∈ U, a • v ∈ U) :
    ∀ a : F.Carrier, ∀ v ∈ U, a • v ∈ U := by
  let R : AddSubgroup F.Carrier :=
    { carrier := {a | ∀ v ∈ U, a • v ∈ U}
      zero_mem' := by intro v hv; simpa only [zero_smul] using U.zero_mem
      add_mem' := by
        intro a b ha hb v hv
        simpa only [add_smul] using U.add_mem (ha v hv) (hb v hv)
      neg_mem' := by
        intro a ha v hv
        simpa only [neg_smul] using U.neg_mem (ha v hv) }
  have hR : AddSubgroup.closure s ≤ R := (AddSubgroup.closure_le _).mpr hstable
  rw [hs] at hR
  exact fun a => hR (show a ∈ (⊤ : AddSubgroup F.Carrier) from trivial)

end NaturalSylowCoordinates

/-- A nonzero normalized subgroup in the upper fixed space forces every
actual Cartan matrix to preserve the upper line. -/
theorem NaturalQuotientMarking.cartan_lowerLeft_eq_zero
    (c : NaturalQuotientMarking T H F) (b : SL(2,F.Carrier))
    (n : NaturalSylowCoordinates T H A F c.multiplicity)
    (he : ∀ (v : omegaClosure T H) (i : Fin c.multiplicity),
      (n.coordinates v).toAdd i = ((c.changeBasis b).coordinates v).toAdd i)
    (U B : Subgroup G)
    (hU : U ≤ omegaClosure T H ⊓ centralizer (A : Set G))
    (hne : U ≠ ⊥) (hcomm : U = ⁅U,B⁆)
    (k : outsideResidual H) (hk : (k : G) ∈ B) :
    (b * c.quotientEquiv (QuotientGroup.mk' _ k) * b⁻¹).val 1 0 = 0 := by
  classical
  obtain ⟨v,hv,hv1⟩ := U.bot_or_exists_ne_one.resolve_left hne
  let w : omegaClosure T H := ⟨v,(hU hv).1⟩
  have hin := (n.mem_fixed_iff w).mp (hU hv).2
  have hex : ∃ i : Fin c.multiplicity, (n.coordinates w).toAdd i 0 ≠ 0 := by
    by_contra! hz
    have hc : n.coordinates w = 1 := by
      apply Multiplicative.toAdd.injective
      ext i j
      fin_cases j
      · exact hz i
      · exact hin i
    have hw : w = 1 := n.coordinates.injective (hc.trans n.coordinates.map_one.symm)
    exact hv1 (congrArg Subtype.val hw)
  obtain ⟨i,hi⟩ := hex
  have hn : B ≤ normalizer (U : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr hcomm.ge
  have hw'U : (residualAction T H k w : G) ∈ U :=
    (mem_normalizer_iff.mp (hn hk) v).mp hv
  have hout := (n.mem_fixed_iff (residualAction T H k w)).mp (hU hw'U).2
  have h := congrFun (c.compatibleSylow_intertwines b n he k w i) 1
  have hz : (b * c.quotientEquiv (QuotientGroup.mk' _ k) * b⁻¹).val 1 0 *
      (n.coordinates w).toAdd i 0 = 0 := by
    simpa only [mulVec,dotProduct,Fin.sum_univ_two,hin i,hout i,mul_zero,add_zero]
      using h.symm
  exact (mul_eq_zero.mp hz).resolve_right hi

/-- The genuine Cartan action and commutator equation give scalar closure.
No upper-triangular placement is assumed: fixation of U and its conjugates
suffices for the pointwise matrix calculation. -/
theorem NaturalQuotientMarking.subgroupImage_smul_mem
    (c : NaturalQuotientMarking T H F) (b : SL(2,F.Carrier))
    (n : NaturalSylowCoordinates T H A F c.multiplicity)
    (he : ∀ (v : omegaClosure T H) (i : Fin c.multiplicity),
      (n.coordinates v).toAdd i = ((c.changeBasis b).coordinates v).toAdd i)
    (U B : Subgroup G)
    (hU : U ≤ omegaClosure T H ⊓ centralizer (A : Set G))
    (hcomm : U = ⁅U,B⁆)
    (hspan : AddSubgroup.closure (cartanScalarSet c b B) = ⊤) :
    ∀ a : F.Carrier, ∀ v ∈ n.subgroupImage U, a • v ∈ n.subgroupImage U := by
  have hn : B ≤ normalizer (U : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr hcomm.ge
  apply NaturalSylowCoordinates.smul_mem_of_scalar_span _ _ hspan
  rintro a ⟨k,hk,rfl⟩ v hv
  change Multiplicative.ofAdd v ∈
    (U.subgroupOf (omegaClosure T H)).map n.coordinates.toMonoidHom at hv
  obtain ⟨w,hw,hwv⟩ := hv
  have hwv' : (n.coordinates w).toAdd = v := congrArg Multiplicative.toAdd hwv
  subst v
  have hwU : (w : G) ∈ U := hw
  let w' := residualAction T H k w
  have hw'U : (w' : G) ∈ U :=
    (mem_normalizer_iff.mp (hn hk) (w : G)).mp hwU
  have hin := (n.mem_fixed_iff w).mp (hU hwU).2
  have hout := (n.mem_fixed_iff w').mp (hU hw'U).2
  have hcoords : (n.coordinates w').toAdd =
      (b * c.quotientEquiv (QuotientGroup.mk' _ k) * b⁻¹).val 0 0 •
        (n.coordinates w).toAdd := by
    ext i j
    fin_cases j
    · have h := congrFun (c.compatibleSylow_intertwines b n he k w i) 0
      change (n.coordinates w').toAdd i 0 = _ * (n.coordinates w).toAdd i 0
      simpa only [mulVec,dotProduct,Fin.sum_univ_two,hin i,mul_zero,add_zero] using h
    · change (n.coordinates w').toAdd i 1 = _ * (n.coordinates w).toAdd i 1
      rw [hin i,hout i,mul_zero]
  exact hcoords ▸ (n.mem_subgroupImage U w').mpr hw'U

/-- Scalar closure and the original order q identify a field line. -/
theorem NaturalQuotientMarking.fieldLine_of_cartan_span
    (c : NaturalQuotientMarking T H F) (b : SL(2,F.Carrier))
    (n : NaturalSylowCoordinates T H A F c.multiplicity)
    (he : ∀ (v : omegaClosure T H) (i : Fin c.multiplicity),
      (n.coordinates v).toAdd i = ((c.changeBasis b).coordinates v).toAdd i)
    (U B : Subgroup G)
    (hU : U ≤ omegaClosure T H ⊓ centralizer (A : Set G))
    (hcomm : U = ⁅U,B⁆) (hcard : Nat.card U = Nat.card F.Carrier)
    (hspan : AddSubgroup.closure (cartanScalarSet c b B) = ⊤) :
    ∃ E : Submodule F.Carrier (Fin c.multiplicity → Fin 2 → F.Carrier),
      Module.finrank F.Carrier E = 1 ∧ E ≤ n.fixedSpace ∧ n.liftSpace E = U := by
  let E : Submodule F.Carrier (Fin c.multiplicity → Fin 2 → F.Carrier) :=
    { n.subgroupImage U with
      smul_mem' := c.subgroupImage_smul_mem b n he U B hU hcomm hspan }
  have hE : E ≤ n.fixedSpace := by
    intro v hv
    obtain ⟨w,hw,rfl⟩ := hv
    exact (n.mem_fixed_iff w).mp (hU hw).2
  have hEU : n.liftSpace E = U := by
    apply le_antisymm
    · intro v hv
      have hvW := n.liftSpace_le E hv
      exact (n.mem_subgroupImage U ⟨v,hvW⟩).mp
        ((n.mem_liftSpace E ⟨v,hvW⟩).mp hv)
    · intro v hv
      have hvW := (hU hv).1
      exact (n.mem_liftSpace E ⟨v,hvW⟩).mpr
        ((n.mem_subgroupImage U ⟨v,hvW⟩).mpr hv)
  refine ⟨E,?_,hE,hEU⟩
  have hsize : Nat.card E = Nat.card F.Carrier := by
    rw [← Nat.card_congr (n.liftSpaceEquiv E), hEU, hcard]
  have hp := Module.natCard_eq_pow_finrank (K := F.Carrier) (V := E)
  apply Nat.pow_right_injective (show 2 ≤ Nat.card F.Carrier by
    have := Finite.one_lt_card (α := F.Carrier); omega)
  simpa only [pow_one] using hp.symm.trans hsize

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
