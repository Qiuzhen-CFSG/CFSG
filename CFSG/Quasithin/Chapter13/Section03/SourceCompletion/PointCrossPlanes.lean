module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.PointMovement
public import Theory.Representation.G2BinaryPointCrossPlanes
public import Theory.GroupTheory.ConjugateIntersectionPlaneCore
/-!
# Cross-hyperplane centralization in the original unitary pair

A moving seed vector gives a plane in the native hyperplane displacement.
The literal automizer lifts that plane and its point-parabolic conjugator
back to the original group. The two abelian module conjugates centralize
their intersection, so the internally conjugate pair would lie in the
plane normalizer's two-core. This contradicts its Baer–Suzuki choice.

Every image and lift uses the original module marking and Q_H. The earlier
plane-core containment is discharged by PointPlaneCore, and the resulting
cross-centralization feeds the full layer-exchange contradiction.
Source: Aschbacher–Smith, Lemma 13.3.18, printed p.895.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open Subgroup ChapterE Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
open Atlas.G2.Natural.BinaryPointFlag
variable {G:Type*} [Group G] {V:Subgroup G} [IsElementaryAbelian 2 V]

theorem point_restricted_displacement_le_commutator
    (C A:Subgroup G) (rho:Automizer V→*Atlas.G2.Model F) (E:Additive V≃ₗ[F]W)
    (he:∀a v,E (automizerRepresentation V a v)=
      Atlas.G2.Restricted.NaturalCoordinates.action F (rho a) (E v)) :
    subspaceCommutator (Atlas.G2.Restricted.NaturalCoordinates.action F)
      (pointCoordinateSubspace E C) ((inducedAutomizer V A).map rho)≤
        pointCoordinateSubspace E ⁅C,A⁆ := by
  apply Submodule.span_le.mpr
  rintro w ⟨_,⟨a,⟨n,hnA,rfl⟩,rfl⟩,v,hv,rfl⟩
  obtain ⟨v,rfl⟩:=E.surjective v
  have hvC: (v.toMul:G)∈C := (mem_pointCoordinateSubspace E C v).mp hv
  rw [←he,←map_sub]
  apply (mem_pointCoordinateSubspace E ⁅C,A⁆ _).mpr
  simp only [toMul_sub,div_eq_mul_inv]
  change (n:G)*v.toMul.val*(n:G)⁻¹*v.toMul.val⁻¹∈⁅C,A⁆
  rw [commutator_comm]
  exact commutator_mem_commutator hnA hvC

theorem pointCoordinateSubspace_mono (E:Additive V≃ₗ[F]W)
    {C A:Subgroup G} (h:C≤A) : pointCoordinateSubspace E C≤pointCoordinateSubspace E A := by
  intro w hw
  obtain ⟨v,rfl⟩:=E.surjective w
  exact (mem_pointCoordinateSubspace E A v).mpr (h ((mem_pointCoordinateSubspace E C v).mp hw))

theorem pointCoordinateSubspace_map_actor
    (C:Subgroup G) (rho:Automizer V→*Atlas.G2.Model F) (E:Additive V≃ₗ[F]W)
    (he:∀a v,E (automizerRepresentation V a v)=
      Atlas.G2.Restricted.NaturalCoordinates.action F (rho a) (E v))
    (n:normalizer (V:Set G)) :
    (pointCoordinateSubspace E C).map (Atlas.G2.Restricted.NaturalCoordinates.action F
      (rho (V.normalizerMonoidHom.rangeRestrict n)))≤
      pointCoordinateSubspace E (C.map (MulAut.conj n.val).toMonoidHom) := by
  rintro _ ⟨w,hw,rfl⟩
  obtain ⟨v,rfl⟩:=E.surjective w
  rw [←he,mem_pointCoordinateSubspace]
  exact mem_map_of_mem (MulAut.conj n.val).toMonoidHom
    ((mem_pointCoordinateSubspace E C v).mp hw)

/-- Actual point-core movement forces the marked plane into an actual
conjugate of the intersection, retaining the lift inside the original J. -/
theorem moving_seed_forces_intersection_plane
    (U B C Q J A X:Subgroup G)
    (rho:Automizer V→*Atlas.G2.Model F) (E:Additive V≃ₗ[F]W)
    (he:∀a v,E (automizerRepresentation V a v)=
      Atlas.G2.Restricted.NaturalCoordinates.action F (rho a) (E v))
    (hUV:U≤V) (hBV:B≤V)
    (hs:pointCoordinateSubspace E U=seed)
    (hp:pointCoordinateSubspace E B=plane)
    (hc:pointCoordinateSubspace E C=hyperplane)
    (hAQ:A≤Q) (hQN:Q≤normalizer (V:Set G))
    (hJQ:J≤normalizer (Q:Set G))
    (hQ:(inducedAutomizer V Q).map rho≤Atlas.G2.unipotent)
    (hP:Atlas.G2.BinaryParabolicPair.derivedSecondAmbient≤(inducedAutomizer V J).map rho)
    (hcom:⁅C,A⁆≤V⊓X) (hm:¬A≤centralizer (U:Set G)) :
    ∃n∈J,n∈normalizer (V:Set G) ∧
      B≤(V⊓X).map (MulAut.conj n).toMonoidHom := by
  let f:(normalizer (V:Set G))→*Atlas.G2.Model F:=
    rho.comp V.normalizerMonoidHom.rangeRestrict
  let Qm:Subgroup (Atlas.G2.Model F):=(inducedAutomizer V Q).map rho
  let Am:Subgroup (Atlas.G2.Model F):=(inducedAutomizer V A).map rho
  have hAm:Am≤Qm:=map_mono (map_mono (comap_mono hAQ))
  have hn:Atlas.G2.BinaryParabolicPair.derivedSecondAmbient≤normalizer (Qm:Set _) := by
    have hN:J.subgroupOf (normalizer (V:Set G))≤
        normalizer (Q.subgroupOf (normalizer (V:Set G)):Set (normalizer (V:Set G))) := by
      intro j hj
      apply mem_normalizer_iff.mpr
      intro q
      exact mem_normalizer_iff.mp (hJQ hj) q.val
    exact hP.trans ((map_mono ((map_mono hN).trans
      ((Q.subgroupOf (normalizer (V:Set G))).le_normalizer_map
        V.normalizerMonoidHom.rangeRestrict))).trans
      ((inducedAutomizer V Q).le_normalizer_map rho))
  have hm':∃x∈Am,∃v∈seed,Atlas.G2.Restricted.NaturalCoordinates.action F x v≠v := by
    by_contra hzero
    push Not at hzero
    apply hm
    intro a ha u hu
    let n:normalizer (V:Set G):=⟨a,hQN (hAQ ha)⟩
    let i:Automizer V:=V.normalizerMonoidHom.rangeRestrict n
    let v:Additive V:=Additive.ofMul ⟨u,hUV hu⟩
    have hi:rho i∈Am:=⟨i,⟨n,ha,rfl⟩,rfl⟩
    have hv:E v∈seed:=hs ▸ (mem_pointCoordinateSubspace E U v).mpr hu
    have heq:=hzero (rho i) hi (E v) hv
    rw [←he] at heq
    have hh:a*u*a⁻¹=u:=congrArg (fun w:Additive V=>(w.toMul:G)) (E.injective heq)
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  obtain ⟨a,ha,hplane⟩:=cross_displacement_contains_conjugate_plane Am Qm hAm hQ
    (hn Atlas.G2.Natural.BinaryPointFlag.point_actor_membership.2.1) hm'
  obtain ⟨i,⟨n,hnJ,rfl⟩,rfl⟩:=hP ha
  refine ⟨n.val,hnJ,n.prop,?_⟩
  have hd:subspaceCommutator (Atlas.G2.Restricted.NaturalCoordinates.action F)
      hyperplane Am≤pointCoordinateSubspace E (V⊓X) := by
    rw [←hc]
    exact (point_restricted_displacement_le_commutator C A rho E he).trans
      (pointCoordinateSubspace_mono E hcom)
  have hb:pointCoordinateSubspace E B≤
      pointCoordinateSubspace E ((V⊓X).map (MulAut.conj n.val).toMonoidHom) := by
    rw [hp]
    exact hplane.trans ((Submodule.map_mono hd).trans
      (pointCoordinateSubspace_map_actor (V⊓X) rho E he n))
  intro b hbB
  let v:Additive V:=Additive.ofMul ⟨b,hBV hbB⟩
  exact (mem_pointCoordinateSubspace E _ v).mp (hb
    ((mem_pointCoordinateSubspace E B v).mpr hbB))


variable [Finite G]
omit [IsElementaryAbelian 2 V] in
/-- In the literal F.9 pair, a moving conjugate hyperplane forces the
original pair into the plane normalizer's two-core. -/
theorem source_cross_hyperplane_centralizes_seed
    {D:ChapterF.Section09.Setup G} (h:D.Hypothesis) :
    let :=h.elementary
    ∀ (rho:Automizer D.V→*Atlas.G2.Model F) (E:Additive D.V≃ₗ[F]W),
    (∀a v,E (automizerRepresentation D.V a v)=
      Atlas.G2.Restricted.NaturalCoordinates.action F (rho a) (E v)) →
    ∀B:Subgroup G, B≤D.V →
    pointCoordinateSubspace E D.Vplus=seed →
    pointCoordinateSubspace E B=plane →
    pointCoordinateSubspace E (D.V⊓D.QH)=hyperplane →
    (inducedAutomizer D.V (D.T:Subgroup G)).map rho≤Atlas.G2.unipotent →
    Atlas.G2.BinaryParabolicPair.derivedSecondAmbient≤
      (inducedAutomizer D.V (D.L₁⊔(D.T:Subgroup G))).map rho →
    D.V≤(normalizer (B:Set G)).pCoreIn 2 →
    ∀g∈D.H,g∈D.V⊔D.V.map (MulAut.conj g).toMonoidHom →
    ¬IsPGroup 2 (D.V⊔D.V.map (MulAut.conj g).toMonoidHom:Subgroup G) →
    (D.V⊓D.QH).map (MulAut.conj g).toMonoidHom≤centralizer (D.Vplus:Set G) := by
  let :=h.elementary
  dsimp only
  intro rho E he B hBV hs hp hc hT hP hcore g hg hin hnot
  let f: G→*G:=(MulAut.conj g).toMonoidHom
  let X:=D.V.map f
  let A:Subgroup G:=(D.V⊓D.QH).map f
  have hQ:D.QH.map f=D.QH:=mem_normalizer_iff_map_conj_eq.mp
    (ChapterF.Section09.Setup.Hypothesis.H_normalizes_QH (D:=D) hg)
  have hA:A=X⊓D.QH:=by
    dsimp only [A,X]
    rw [map_inf _ _ _ (MulAut.conj g).injective,hQ]
  have hAQ:A≤D.QH:=hA ▸ inf_le_right
  have hAX:A≤X:=map_mono inf_le_left
  have hQN:D.QH≤normalizer (D.V:Set G):=h.QH_le_T.trans h.T_normalizes_V
  have hQX:D.QH≤normalizer (X:Set G):=by
    rw [←hQ]
    exact (map_mono hQN).trans (D.V.le_normalizer_map f)
  have hcom:⁅D.V⊓D.QH,A⁆≤D.V⊓X:=le_inf
    ((commutator_mono inf_le_left le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp (hAQ.trans hQN)))
    ((commutator_mono le_rfl hAX).trans
      (le_normalizer_iff_commutator_le_right.mp (inf_le_right.trans hQX)))
  by_contra hm
  obtain ⟨n,hnJ,hnV,hnB⟩:=moving_seed_forces_intersection_plane
    D.Vplus B (D.V⊓D.QH) D.QH (D.L₁⊔(D.T:Subgroup G)) A X
    rho E he h.plus_le hBV hs hp hc hAQ hQN
    (h.local_le.trans ChapterF.Section09.Setup.Hypothesis.H_normalizes_QH)
    ((map_mono (map_mono (comap_mono h.QH_le_T))).trans hT) hP hcom hm
  exact hnot (pair_isTwo_of_conjugate_intersection_plane D.V B g n hin hnV hnB hcore)
end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
