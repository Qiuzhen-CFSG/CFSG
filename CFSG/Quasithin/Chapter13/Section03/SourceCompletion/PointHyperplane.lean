module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.PointAction
public import Theory.GroupTheory.SubgroupPartitionCounting
public import CFSG.Quasithin.ChapterE.Section03.Parameters.AutomizerFF
public import Theory.Representation.G2BinaryPointFlag

/-!
# The literal core intersection in the unitary point-parabolic frame

Coordinate transport identifies subgroups of the original V with binary
subspaces without changing their cardinalities. Normality of the original
Q_H makes V∩Q_H invariant under L₁T, so the native interval leaves V₃,V₅,V.
Hall–Witt excludes V₃ after the smaller closure is proved elementary; the
nonabelian-closure branch excludes V. The surviving subgroup has order 32
and relative corank one in the original V.

The movement lower bound is an intermediate input here and is discharged
by the literal native displacement transport in PointMovement. The F.9
setup, original module frame, and prior 13.3.17 noncentrality retain their
source meanings.

Source: Aschbacher–Smith, Lemma 13.3.18, printed p.895.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open Subgroup ChapterE
open scoped IsMulCommutative
open Atlas.G2.Natural.BinaryPointFlag
variable {G:Type*} [Group G] {V:Subgroup G} [IsElementaryAbelian 2 V]

def pointCoordinateSubspace (E:Additive V≃ₗ[F]W) (A:Subgroup G) : Submodule F W :=
  (AddSubgroup.toZModSubmodule 2 (A.subgroupOf V).toAddSubgroup).map E.toLinearMap

@[simp] theorem mem_pointCoordinateSubspace (E:Additive V≃ₗ[F]W) (A:Subgroup G)
    (v:Additive V) : E v∈pointCoordinateSubspace E A ↔ (v.toMul:G)∈A := by
  constructor
  · rintro ⟨w,hw,he⟩
    have hwv : w=v := E.injective he
    exact hwv ▸ hw
  · intro hv
    exact ⟨v,hv,rfl⟩

theorem pointCoordinateSubspace_injective (E:Additive V≃ₗ[F]W)
    {A B:Subgroup G} (hA:A≤V) (hB:B≤V)
    (h:pointCoordinateSubspace E A=pointCoordinateSubspace E B) : A=B := by
  ext x
  constructor
  · intro hx
    exact (mem_pointCoordinateSubspace E B (Additive.ofMul ⟨x,hA hx⟩)).mp
      (h ▸ (mem_pointCoordinateSubspace E A _).mpr hx)
  · intro hx
    exact (mem_pointCoordinateSubspace E A (Additive.ofMul ⟨x,hB hx⟩)).mp
      (h.symm ▸ (mem_pointCoordinateSubspace E B _).mpr hx)

theorem pointCoordinateSubspace_self (E:Additive V≃ₗ[F]W) :
    pointCoordinateSubspace E V=⊤ := by
  apply top_unique
  intro w _
  obtain ⟨v,rfl⟩:=E.surjective w
  exact (mem_pointCoordinateSubspace E V v).mpr v.toMul.prop

/-- The native point-parabolic interval transported to the literal ambient
subgroup, using actual lifts in L₁T rather than invariant-space assumptions. -/
theorem point_invariant_interval_ambient
    (rho:Automizer V→*Atlas.G2.Model F) (E:Additive V≃ₗ[F]W)
    (he:∀a v,E (automizerRepresentation V a v)=
      Atlas.G2.Restricted.NaturalCoordinates.action F (rho a) (E v))
    (B J A:Subgroup G) (hBA:B≤A) (hAV:A≤V)
    (hB:pointCoordinateSubspace E B=seed)
    (hn:J≤normalizer (A:Set G))
    (hP:Atlas.G2.BinaryParabolicPair.derivedSecondAmbient≤(inducedAutomizer V J).map rho) :
    A=B ∨ pointCoordinateSubspace E A=hyperplane ∨ A=V := by
  have hseed : seed≤pointCoordinateSubspace E A := by
    rw [←hB]
    intro v hv
    obtain ⟨w,rfl⟩:=E.surjective v
    exact (mem_pointCoordinateSubspace E A w).mpr
      (hBA ((mem_pointCoordinateSubspace E B w).mp hv))
  have hinv : ∀a∈Atlas.G2.BinaryParabolicPair.derivedSecondAmbient,
      ∀v∈pointCoordinateSubspace E A,
      Atlas.G2.Restricted.NaturalCoordinates.action F a v∈pointCoordinateSubspace E A := by
    intro a ha v hv
    obtain ⟨b,⟨n,hnJ,rfl⟩,rfl⟩:=hP ha
    obtain ⟨w,rfl⟩:=E.surjective v
    rw [←he,mem_pointCoordinateSubspace]
    exact (mem_normalizer_iff.mp (hn hnJ) w.toMul.val).mp
      ((mem_pointCoordinateSubspace E A w).mp hv)
  rcases Atlas.G2.Natural.BinaryPointFlag.point_invariant_interval
    (pointCoordinateSubspace E A) hseed hinv with hh|hh|hh
  · left
    exact pointCoordinateSubspace_injective E hAV (hBA.trans hAV) (hh.trans hB.symm)
  · exact Or.inr (Or.inl hh)
  · right;right
    exact pointCoordinateSubspace_injective E hAV le_rfl
      (hh.trans (pointCoordinateSubspace_self E).symm)
variable [Finite G]

private noncomputable def coordinateSubspaceEquiv
    (E:Additive V≃ₗ[F]W) (A:Subgroup G) (hAV:A≤V) : A≃pointCoordinateSubspace E A where
  toFun a := ⟨E (Additive.ofMul ⟨a.val,hAV a.prop⟩),(mem_pointCoordinateSubspace E A _).mpr a.prop⟩
  invFun x := ⟨(E.symm x.val).toMul.val,(mem_pointCoordinateSubspace E A (E.symm x.val)).mp
    (by simpa only [LinearEquiv.apply_symm_apply] using x.prop)⟩
  left_inv a := by simp
  right_inv x := by simp

omit [Finite G] in
/-- The coordinate correspondence retains the actual subgroup order. -/
theorem card_pointCoordinateSubspace (E:Additive V≃ₗ[F]W)
    (A:Subgroup G) (hAV:A≤V) : Nat.card (pointCoordinateSubspace E A)=Nat.card A :=
  (Nat.card_congr (coordinateSubspaceEquiv E A hAV)).symm

omit [Finite G] in
/-- The native hyperplane identification gives the literal relative corank. -/
theorem corank_one_of_point_hyperplane (E:Additive V≃ₗ[F]W)
    (A:Subgroup G) (hAV:A≤V) (hA:pointCoordinateSubspace E A=hyperplane) :
    subgroupCorank V A=1 := by
  have hcard : Nat.card A=32 := by
    rw [←card_pointCoordinateSubspace E A hAV,hA,card_hyperplane]
  have hV : Nat.card V=64 := by
    rw [Nat.card_congr (Additive.ofMul:V≃Additive V),Nat.card_congr E.toEquiv]
    simp
  have hi:=relIndex_mul_card_of_le hAV
  rw [hcard,hV] at hi
  have hi2:A.relIndex V=2 := by omega
  simp only [subgroupCorank,hi2]
  decide


omit [IsElementaryAbelian 2 V] in
/-- The original core intersection is the native hyperplane. Its invariance
comes from the actual L₁T and Q_H; Hall–Witt excludes the smaller seed, and
the nonabelian-closure branch excludes the whole module. -/
theorem core_intersection_point_hyperplane
    {D:ChapterF.Section09.Setup G} (h:D.Hypothesis) :
    let :=h.elementary
    ∀ (rho:Automizer D.V→*Atlas.G2.Model F) (E:Additive D.V≃ₗ[F]W),
    (∀a v,E (automizerRepresentation D.V a v)=
      Atlas.G2.Restricted.NaturalCoordinates.action F (rho a) (E v)) →
    pointCoordinateSubspace E D.Vplus=seed →
    (inducedAutomizer D.V (D.T:Subgroup G)).map rho≤Atlas.G2.unipotent →
    Atlas.G2.BinaryParabolicPair.derivedSecondAmbient≤
      (inducedAutomizer D.V (D.L₁⊔(D.T:Subgroup G))).map rho →
    (∀g∈D.H,⁅D.V,D.V.map (MulAut.conj g).toMonoidHom⁆≤
      D.V⊓D.V.map (MulAut.conj g).toMonoidHom →
      ⁅D.V,D.V.map (MulAut.conj g).toMonoidHom⁆=⊥) →
    ¬IsMulCommutative D.VH → D.Vplus≤⁅D.V,D.UH⁆ →
    ¬D.Vplus≤centralizer (D.QH:Set G) →
    pointCoordinateSubspace E (D.V⊓D.QH)=hyperplane ∧
      subgroupCorank D.V (D.V⊓D.QH)=1 := by
  let :=h.elementary
  dsimp only
  intro rho E he hs hT hP hcomm hnonabelian hmove hnoncentral
  have hseed (v:Additive D.V) : E v∈seed ↔ (v.toMul:G)∈D.Vplus := by
    rw [←hs,mem_pointCoordinateSubspace]
  let :IsElementaryAbelian 2 D.UH :=
    seed_closure_elementary_of_point_action h rho E he hseed hT hP
  have hBA:D.Vplus≤D.V⊓D.QH :=
    le_inf h.plus_le ((le_conjugateSpanBy D.Vplus D.H).trans h.UH_le_QH)
  have hLV:D.L₁⊔(D.T:Subgroup G)≤normalizer (D.V:Set G) :=
    (le_inf h.local_le h.local_normalizes).trans (h.normalizer_control.trans inf_le_right)
  have hLQ:D.L₁⊔(D.T:Subgroup G)≤normalizer (D.QH:Set G) :=
    h.local_le.trans ChapterF.Section09.Setup.Hypothesis.H_normalizes_QH
  have hn:D.L₁⊔(D.T:Subgroup G)≤normalizer (D.V⊓D.QH:Set G) :=
    (le_inf hLV hLQ).trans inf_normalizer_le_normalizer_inf
  have hcases:=point_invariant_interval_ambient rho E he D.Vplus
    (D.L₁⊔(D.T:Subgroup G)) (D.V⊓D.QH) hBA inf_le_left hs hn hP
  have hh:pointCoordinateSubspace E (D.V⊓D.QH)=hyperplane := by
    rcases hcases with hsmall|hmiddle|hbig
    · exfalso
      apply core_intersection_not_centralizes_seed_closure h hmove hnoncentral
      rw [hsmall]
      exact (le_conjugateSpanBy D.Vplus D.H).trans (le_centralizer D.UH)
    · exact hmiddle
    · exact (hnonabelian (closure_abelian_of_le_core h hcomm (inf_eq_left.mp hbig))).elim
  exact ⟨hh,corank_one_of_point_hyperplane E _ inf_le_left hh⟩

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
