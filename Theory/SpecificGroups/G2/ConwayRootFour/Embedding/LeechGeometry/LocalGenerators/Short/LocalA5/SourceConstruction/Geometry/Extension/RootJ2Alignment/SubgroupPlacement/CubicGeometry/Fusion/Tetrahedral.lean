module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Reduction
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Tetrahedral.Reference
public import Theory.SpecificGroups.Alternating.FourPairAutomorphisms
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# Transporting reference tetrahedral geometry through ambient cubic fusion

Ambient fusion moves a cubic to the literal reference cubic. Reference orbit
control then corrects this conjugator to normalize the literal scalar I.
Conjugation by that corrected element transports both the subgroup orbit and
the pointwise normalizer action back to the original cubic centralizer.

Only one outer actor is required at the reference: Aut(A₄) has order 24 and
its inner subgroup has order 12. The two cosets show that the inner actions,
already realized by I, and that single outer action realize every automorphism.
All centralizers are pointwise centralizers, and all maps use left conjugation.

The two reference model premises remain unproved here. In particular, this
module does not identify scalarFour.range, or an arbitrary ambient conjugate,
with the root-A₄ class inside the reference centralizer. It is conditional
assembly for the separate concrete orbit and outer-actor constructions.

Source: Aschbacher, *Sporadic Groups* (1994), 48.3 (pp.268–269),
49.1–49.2 (p.280), and the normalizer step of 49.5 (p.284).
-/

@[expose] public noncomputable section
open Subgroup Atlas.Conway
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion

variable {G : Type*} [Group G]
private def cMap (g : G) (J : Subgroup G) := J.map (MulAut.conj g).toMonoidHom
private theorem cMap_mul (g h : G) (J : Subgroup G) :
    cMap (g*h) J = cMap g (cMap h J) := by
  rw [cMap, cMap, cMap, map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]
private theorem cMap_one (J : Subgroup G) : cMap 1 J = J := by
  ext z
  simp [cMap, Subgroup.mem_map]
private theorem cMap_inv (g : G) (J : Subgroup G) :
    cMap g⁻¹ (cMap g J) = J := by rw [← cMap_mul]; simp [cMap_one]
private theorem centralizes_transport (g : G) {P J : Subgroup G}
    (h : P ≤ centralizer (J : Set G)) :
    cMap g P ≤ centralizer (cMap g J : Set G) := by
  rintro _ ⟨p,hp,rfl⟩ _ ⟨j,hj,rfl⟩
  exact (MulAut.conj g).map_mul j p ▸ (MulAut.conj g).map_mul p j ▸
    congrArg (MulAut.conj g) (h hp j hj)
private theorem centralizer_transport (g : G) {P : Subgroup G} {c : G}
    (hc : c ∈ centralizer (P : Set G)) :
    MulAut.conj g c ∈ centralizer (cMap g P : Set G) := by
  rintro _ ⟨p,hp,rfl⟩
  exact (MulAut.conj g).map_mul p c ▸ (MulAut.conj g).map_mul c p ▸
    congrArg (MulAut.conj g) (hc p hp)
private theorem cMap_centralizer {P : Subgroup G} {c : G}
    (hc : c ∈ centralizer (P : Set G)) : cMap c P = P :=
  mem_normalizer_iff_map_conj_eq.mp (centralizer_le_normalizer _ hc)
private theorem cMap_normalizer {J : Subgroup G} {g : G}
    (hg : g ∈ normalizer (J : Set G)) : cMap g J = J :=
  mem_normalizer_iff_map_conj_eq.mp hg

private theorem aligned_conjugator (J P Q : Subgroup G)
    (hP : P ≤ centralizer (J : Set G)) (g : G) (hPQ : P = cMap g Q)
    (hQorbit : ∀ h : G, Q ≤ centralizer (cMap h J : Set G) →
      ∃ c ∈ centralizer (Q : Set G), cMap c (cMap h J) = J) :
    ∃ x ∈ normalizer (J : Set G), P = cMap x Q := by
  have hQJ : Q ≤ centralizer (cMap g⁻¹ J : Set G) := by
    have h := centralizes_transport g⁻¹ hP
    rwa [hPQ, cMap_inv] at h
  obtain ⟨c,hc,hcJ⟩ := hQorbit g⁻¹ hQJ
  have hnorm : c*g⁻¹ ∈ normalizer (J : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    change cMap (c*g⁻¹) J = J
    rwa [cMap_mul]
  refine ⟨(c*g⁻¹)⁻¹, (normalizer _).inv_mem hnorm, ?_⟩
  rw [mul_inv_rev, inv_inv, cMap_mul,
    cMap_centralizer ((centralizer (Q : Set G)).inv_mem hc)]
  exact hPQ

private theorem orbit_transport (J P Q : Subgroup G) (x : G)
    (hx : x ∈ normalizer (J : Set G)) (hPQ : P = cMap x Q)
    (hQorbit : ∀ h : G, Q ≤ centralizer (cMap h J : Set G) →
      ∃ c ∈ centralizer (Q : Set G), cMap c (cMap h J) = J) :
    ∀ g : G, P ≤ centralizer (cMap g J : Set G) →
      ∃ c ∈ centralizer (P : Set G), cMap c (cMap g J) = J := by
  intro g hg
  have hQJ : Q ≤ centralizer (cMap (x⁻¹*g) J : Set G) := by
    have h := centralizes_transport x⁻¹ hg
    rwa [hPQ, cMap_inv, ← cMap_mul] at h
  obtain ⟨c,hc,hcJ⟩ := hQorbit (x⁻¹*g) hQJ
  refine ⟨MulAut.conj x c, ?_, ?_⟩
  · rw [hPQ]
    exact centralizer_transport x hc
  · change cMap (x*c*x⁻¹) (cMap g J) = J
    rw [cMap_mul, cMap_mul, ← cMap_mul x⁻¹ g, hcJ, cMap_normalizer hx]

private theorem action_transport (J P Q : Subgroup G) (x : G)
    (hx : x ∈ normalizer (J : Set G)) (hPQ : P = cMap x Q)
    (hQaction : ∀ n ∈ normalizer (J : Set G),
      ∃ d ∈ centralizer (Q : Set G), ∀ i ∈ J, MulAut.conj d i = MulAut.conj n i) :
    ∀ n ∈ normalizer (J : Set G),
      ∃ d ∈ centralizer (P : Set G), ∀ i ∈ J, MulAut.conj d i = MulAut.conj n i := by
  intro n hn
  have hn' : x⁻¹*n*x ∈ normalizer (J : Set G) :=
    (normalizer _).mul_mem ((normalizer _).mul_mem ((normalizer _).inv_mem hx) hn) hx
  obtain ⟨d,hd,hdn⟩ := hQaction (x⁻¹*n*x) hn'
  refine ⟨MulAut.conj x d, ?_, ?_⟩
  · rw [hPQ]
    exact centralizer_transport x hd
  · intro i hi
    have hi' : MulAut.conj x⁻¹ i ∈ J := by
      have hmem : MulAut.conj x⁻¹ i ∈ cMap x⁻¹ J := ⟨i,hi,rfl⟩
      rwa [cMap_normalizer ((normalizer _).inv_mem hx)] at hmem
    have he := congrArg (MulAut.conj x) (hdn _ hi')
    simpa [MulAut.conj_apply, mul_assoc] using he

private def tetrahedralFour : I ≃* alternatingGroup (Fin 4) :=
  tetrahedralEquiv.symm.trans
    (Equiv.altCongrHom (Fintype.equivFinOfCardEq (by
      rw [← Nat.card_eq_fintype_card]
      exact fourPoints_card)))

private theorem tetrahedral_inner_index : (MulAut.innerSubgroup I).index = 2 := by
  have hinj : Function.Injective (MulAut.conj : I →* MulAut I) := by
    intro a b hab
    apply tetrahedralFour.injective
    apply Subtype.val_injective
    apply AlternatingFourPair.conjA_inj
    change MulAut.conjNormal (tetrahedralFour a).val =
      MulAut.conjNormal (tetrahedralFour b).val
    rw [MulAut.conjNormal_val, MulAut.conjNormal_val,
      ← MulAut.congr_conj, ← MulAut.congr_conj, hab]
  have hi : Nat.card (MulAut.innerSubgroup I) = 12 :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm.trans I_card
  have ha : Nat.card (MulAut I) = 24 := by
    rw [Nat.card_congr (MulAut.congr tetrahedralFour).toEquiv,
      ← Nat.card_congr AlternatingFourPair.eA.toEquiv, Nat.card_perm]
    norm_num
  have h := (MulAut.innerSubgroup I).index_mul_card
  rw [hi,ha] at h
  omega

private theorem action_of_outer (P : Subgroup LeechCentralQuotient)
    (hIP : I ≤ centralizer (P : Set LeechCentralQuotient))
    (t : LeechCentralQuotient) (htP : t ∈ centralizer (P : Set LeechCentralQuotient))
    (htI : t ∈ normalizer (I : Set LeechCentralQuotient))
    (htouter : ¬ ∃ j ∈ I, ∀ i ∈ I, MulAut.conj t i = MulAut.conj j i) :
    ∀ n ∈ normalizer (I : Set LeechCentralQuotient),
      ∃ d ∈ centralizer (P : Set LeechCentralQuotient),
        ∀ i ∈ I, MulAut.conj d i = MulAut.conj n i := by
  let θ : MulAut I := I.normalizerMonoidHom ⟨t,htI⟩
  have hθ : θ ∉ MulAut.innerSubgroup I := by
    rintro ⟨j,hj⟩
    apply htouter
    refine ⟨j,j.property,fun i hi => ?_⟩
    exact (congrArg (fun f : MulAut I => (f ⟨i,hi⟩ : LeechCentralQuotient)) hj).symm
  intro n hn
  let α : MulAut I := I.normalizerMonoidHom ⟨n,hn⟩
  by_cases hα : α ∈ MulAut.innerSubgroup I
  · obtain ⟨j,hj⟩ := hα
    refine ⟨j,hIP j.property,fun i hi => ?_⟩
    exact congrArg (fun f : MulAut I => (f ⟨i,hi⟩ : LeechCentralQuotient)) hj
  · have hh : α*θ⁻¹ ∈ MulAut.innerSubgroup I := by
      rw [Subgroup.mul_mem_iff_of_index_two tetrahedral_inner_index]
      simp only [Subgroup.inv_mem_iff, hα, hθ]
    obtain ⟨j,hj⟩ := hh
    have he : MulAut.conj j * θ = α := by rw [hj]; simp
    refine ⟨j*t,(centralizer (P : Set LeechCentralQuotient)).mul_mem
      (hIP j.property) htP,fun i hi => ?_⟩
    have h := congrArg (fun f : MulAut I => (f ⟨i,hi⟩ : LeechCentralQuotient)) he
    change (j : LeechCentralQuotient) * (t*i*t⁻¹) * (j : LeechCentralQuotient)⁻¹ =
      n*i*n⁻¹ at h
    simpa [MulAut.conj_apply, mul_assoc] using h

/-- The single reference outer actor, together with the inner actions of I,
realizes the entire ambient normalizer action in the reference cubic centralizer. -/
theorem referenceNormalizerAction_of_outer (houter : ReferenceOuterAction) :
    ∀ n ∈ normalizer (I : Set LeechCentralQuotient),
      ∃ d ∈ referenceCubicCentralizer,
        ∀ i ∈ I, MulAut.conj d i = MulAut.conj n i := by
  obtain ⟨t,htP,htI,htouter⟩ := houter
  apply action_of_outer (Subgroup.zpowers RootModel.referenceCubic) _ t htP htI htouter
  exact Subgroup.le_centralizer_iff.mp (Subgroup.zpowers_le.mpr RootModel.referenceCubic_mem)

/-- Ambient cubic fusion reduces both universal tetrahedral obligations to two
concrete facts at the literal fixed reference cubic. The latter premises still
require their independent geometric proofs. -/
theorem tetrahedral_conjugacy_of_reference (hamb : AmbientFusion)
    (horbit : ReferenceTetrahedralOrbit) (houter : ReferenceOuterAction) :
    TetrahedralOrbit ∧ TetrahedralNormalizerAction := by
  have haction := referenceNormalizerAction_of_outer houter
  constructor
  · intro a ha hoa hfa
    obtain ⟨g,hg⟩ := hamb a RootModel.referenceCubic hoa RootModel.referenceCubic_order
      hfa RootModel.referenceCubic_fixedFree
    obtain ⟨x,hx,hxP⟩ := aligned_conjugator I (Subgroup.zpowers a)
      (Subgroup.zpowers RootModel.referenceCubic) (Subgroup.zpowers_le.mpr ha) g hg horbit
    exact orbit_transport I (Subgroup.zpowers a) (Subgroup.zpowers RootModel.referenceCubic)
      x hx hxP horbit
  · intro a ha hoa hfa
    obtain ⟨g,hg⟩ := hamb a RootModel.referenceCubic hoa RootModel.referenceCubic_order
      hfa RootModel.referenceCubic_fixedFree
    obtain ⟨x,hx,hxP⟩ := aligned_conjugator I (Subgroup.zpowers a)
      (Subgroup.zpowers RootModel.referenceCubic) (Subgroup.zpowers_le.mpr ha) g hg horbit
    exact action_transport I (Subgroup.zpowers a) (Subgroup.zpowers RootModel.referenceCubic)
      x hx hxP haction

/-- Application to the existing relative-fusion consumer, with precisely the
ambient fusion and the two remaining reference geometry premises explicit. -/
theorem fixedFreeCubicFusion_of_reference (hamb : AmbientFusion)
    (horbit : ReferenceTetrahedralOrbit) (houter : ReferenceOuterAction) :
    FixedFreeCubicFusion := by
  obtain ⟨ho,ha⟩ := tetrahedral_conjugacy_of_reference hamb horbit houter
  exact fixedFreeCubicFusion_of_conjugacy_data hamb ho ha

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion
