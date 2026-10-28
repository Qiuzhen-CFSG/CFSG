module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.LinearUnitaryCartan
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitaryCartanFixed

/-!
# The unitary center torus in an octagon

The commutator of the rank-one two-point torus with its actual root
reflection is cyclic of order 2^b-1 and is inverted by that reflection.
Prime-order centralizer bounds make its action on the unitary root center
faithful. Its regular action is also the full Cartan image on the center.
For odd b, the perpendicular reflection centralizes the conjugate center.
The Weyl word then forces the center torus to inject into the opposite
panel Cartan, giving the remaining field-unit divisibility.

Both special and projective unitary factors are retained, including their
actual scalar projections. Source: Fong--Seitz I (6F), pp.45--46.
-/

public noncomputable section
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure
open Subgroup
open scoped IsMulCommutative
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource

private theorem cyclic_image_of_regular_subgroup
    {H A : Type*} [Group H] [Finite H] [IsMulCommutative H]
    [Group A] [Finite A] [IsElementaryAbelian 2 A]
    (ρ : H →* MulAut A) (C : Subgroup H) [IsCyclic C]
    {b : ℕ} (hb : 0 < b) (hC : Nat.card C = 2^b-1) (hA : Nat.card A = 2^b)
    (hf : Function.Injective (ρ.comp C.subtype)) :
    IsCyclic ρ.range ∧ Nat.card ρ.range = 2^b-1 := by
  classical
  let ι := ρ.comp C.subtype
  have hex : ∃ x : A, x ≠ 1 := by
    have hc : 1 < Nat.card A := by rw [hA]; exact Nat.one_lt_two_pow hb.ne'
    let : Nontrivial A := Finite.one_lt_card_iff_nontrivial.mp hc
    exact exists_ne 1
  obtain ⟨x,hx⟩ := hex
  have he : ι.range = ρ.range := by
    apply le_antisymm
    · rintro _ ⟨c,rfl⟩
      exact ⟨c.val,rfl⟩
    rintro _ ⟨h,rfl⟩
    obtain ⟨c,hc,_⟩ := RootAction.regular_of_card ι hf hb hC hA x (ρ h x) hx
      (fun hh => hx ((ρ h).injective (hh.trans (map_one _).symm)))
    refine ⟨c,?_⟩
    ext y
    by_cases hy : y = 1
    · simp only [hy,map_one]
    obtain ⟨d,hd,_⟩ := RootAction.regular_of_card ι hf hb hC hA x y hx hy
    have hcomm : ρ h * ι d = ι d * ρ h := by
      change ρ h * ρ d.val = ρ d.val * ρ h
      rw [←map_mul,←map_mul,mul_comm h d.val]
    have hcomm' : ι c * ι d = ι d * ι c := by rw [←map_mul,←map_mul,mul_comm c d]
    rw [←hd,show ι c (ι d x) = ι d (ι c x) from DFunLike.congr_fun hcomm' x,hc]
    exact (DFunLike.congr_fun hcomm x).symm
  rw [←he]
  exact ⟨(MonoidHom.ofInjective hf).isCyclic.mp inferInstance,
    (Nat.card_congr (MonoidHom.ofInjective hf).symm.toEquiv).trans hC⟩

variable {Y : Type*} [Group Y] (H A : Subgroup Y)

private theorem inverted_centralizes_of_fixed_root
    (hA : H ≤ normalizer (A : Set Y)) (hodd : Nat.Coprime 2 (Nat.card H))
    (s z : Y) (hz : z ∈ H) (hs : s ∈ centralizer (A : Set Y))
    (hinv : s*z*s⁻¹ = z⁻¹) : z ∈ centralizer (A : Set Y) := by
  have hsq : (RootAction.action H A hA ⟨z,hz⟩)^2 = 1 := by
    apply MulEquiv.ext
    intro a
    apply Subtype.ext
    change z*(z*a*z⁻¹)*z⁻¹ = a
    have hsfix (a : A) : s*a*s⁻¹ = a :=
      (mul_inv_eq_iff_eq_mul.mpr ((mem_centralizer_iff.mp hs) a a.property).symm)
    have hnorm := (mem_normalizer_iff.mp (hA hz) a).mp a.property
    have h := hsfix ⟨z*a*z⁻¹,hnorm⟩
    have hcalc : z⁻¹*a*z = z*a*z⁻¹ := by
      calc
        _ = (s*z*s⁻¹)*(s*a*s⁻¹)*(s*z*s⁻¹)⁻¹ := by rw [hinv,hsfix,inv_inv]
        _ = s*(z*a*z⁻¹)*s⁻¹ := by group
        _ = z*a*z⁻¹ := h
    rw [←hcalc]
    group
  have hod : Nat.Coprime 2 (orderOf (RootAction.action H A hA ⟨z,hz⟩)) :=
    hodd.of_dvd_right ((orderOf_map_dvd _ _).trans (orderOf_dvd_natCard (⟨z,hz⟩ : H)))
  have he : RootAction.action H A hA ⟨z,hz⟩ = 1 :=
    orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hod (orderOf_dvd_of_pow_eq_one hsq) (dvd_refl _))
  have hk : (⟨z,hz⟩ : H) ∈ (RootAction.action H A hA).ker := he
  rwa [RootAction.action_kernel] at hk

variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

private theorem center_torus_dvd_panel (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    {b : ℕ} (hb : Odd b)
    (Z : Subgroup (X ⧸ Q.D))
    (hZdef : Z = (center (simpleRoot Q split j)).map (simpleRoot Q split j).subtype)
    [IsElementaryAbelian 2 Z] (hZcard : Nat.card Z = 2^b)
    (C : Subgroup ↥(Q.tits.B ⊓ Q.tits.N)) [IsCyclic C]
    (hCcard : Nat.card C = 2^b-1)
    (hCinv : ∀ z ∈ C, simpleCartanAction Q split j z = z⁻¹)
    (hCfaith : ∀ z ∈ C, (z : X ⧸ Q.D) ∈ centralizer (Z : Set _) → z = 1)
    (s : ∀ k, HexagonStructure.RootReflection Q split k) :
    2^b-1 ∣ Nat.card (cartanPanelMap Q i).range := by
  let := split.abelian
  let H := Q.tits.B ⊓ Q.tits.N
  have hZH : H ≤ normalizer (Z : Set (X ⧸ Q.D)) := by
    rw [hZdef]
    exact (torus_normalizes_simpleRoot Q split j).trans
      (normalizer_le_normalizer_characteristic_image _ _)
  let ρ := RootAction.action H Z hZH
  have hfaith : Function.Injective (ρ.comp C.subtype) := by
    apply (ρ.comp C.subtype).ker_eq_bot_iff.mp
    apply bot_unique
    intro z hz
    have hk : z.val ∈ ρ.ker := hz
    rw [RootAction.action_kernel] at hk
    exact Subtype.ext (hCfaith z.val z.property hk)
  obtain ⟨hcyc,hcard⟩ := cyclic_image_of_regular_subgroup ρ C hb.pos hCcard hZcard hfaith
  let w := Q.simple i*Q.simple j*Q.simple i
  let n := representative w
  let nH : normalizer (H : Set (X ⧸ Q.D)) := ⟨n,torus_normalizes n⟩
  let A := rightConjugate Z (n : X ⧸ Q.D)
  have hAH := RootAction.normalizes_conjugate H Z hZH nH
  let α := RootAction.action H A hAH
  let ec := RootAction.conjugateImageEquiv H Z hZH nH
  let eA := RootAction.conjugateEquiv Z n
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_injective eA.toMonoidHom eA.injective
  let : IsCyclic α.range := ec.isCyclic.mpr hcyc
  let r := involutoryRootReflection Q split j (s j)
  have hAdef : A = (center (rootAt Q split j w)).map (rootAt Q split j w).subtype := by
    rw [show A=rightConjugate Z (n : X ⧸ Q.D) from rfl,hZdef,
      QuadrangleStructure.rightConjugate_center]
    rfl
  have hrA : (r.val : X ⧸ Q.D) ∈ normalizer (A : Set (X ⧸ Q.D)) := by
    rw [hAdef]
    exact (normalizer_le_normalizer_characteristic_image _ _)
      (perpendicular_root_normalizes Q split hm j i hij.symm r.val r.class_eq)
  have hrC : (r.val : X ⧸ Q.D) ∈ centralizer (A : Set (X ⧸ Q.D)) := by
    apply RootAction.normalizing_involution_centralizes H A hAH hb
    · exact (Nat.card_congr ec.toEquiv).trans hcard
    · exact (Nat.card_congr eA.toEquiv).trans hZcard
    · exact hrA
    · exact torus_normalizes r.val
    · exact involutoryRootReflection_sq Q split j (s j)
  let f := (cartanPanelMap Q i).rangeRestrict.comp C.subtype
  have hf : Function.Injective f := by
    apply f.ker_eq_bot_iff.mp
    apply bot_unique
    intro z hz
    have hzker : z.val ∈ (cartanPanelMap Q i).ker := congrArg Subtype.val hz
    have hzi : simpleCartanAction Q split i z.val = z.val :=
      cartanPanelMap_kernel_le_fixed Q split i (s i) hzker
    have hzj := hCinv z.val z.property
    have hrinv : (r.val : X ⧸ Q.D)*(z.val : X ⧸ Q.D)*(r.val : X ⧸ Q.D)⁻¹ =
        (z.val : X ⧸ Q.D)⁻¹ := by
      have hraw := congrArg (fun h : H => (h : X ⧸ Q.D)) hzj
      rw [simpleCartanAction_apply Q split j r.val r.class_eq] at hraw
      have hrself : (r.val : X ⧸ Q.D)⁻¹ = r.val :=
        inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using (involutoryRootReflection_sq Q split j (s j)))
      simpa only [hrself,Subgroup.coe_inv] using hraw
    have hzA := inverted_centralizes_of_fixed_root H A hAH split.odd
      r.val z.val z.val.property hrC hrinv
    have hα : α z.val = 1 := by
      change z.val ∈ α.ker
      rw [RootAction.action_kernel]
      exact hzA
    have hword : H.normalizerMonoidHom nH z.val = z.val⁻¹ := by
      change normalizerCartanAction Q n z.val = _
      rw [←weylCartanAction_lift Q split n,representative_spec]
      change weylCartanAction Q split ((Q.simple i*Q.simple j)*Q.simple i) z.val = _
      rw [map_mul,map_mul]
      change simpleCartanAction Q split i (simpleCartanAction Q split j
        (simpleCartanAction Q split i z.val)) = _
      rw [hzi,hzj,map_inv,hzi]
    have hc := DFunLike.congr_fun (RootAction.conjugate_action H Z hZH nH) z.val
    change MulAut.congr eA (α z.val) = ρ (H.normalizerMonoidHom nH z.val) at hc
    rw [hα,map_one,hword,map_inv] at hc
    have hρ : ρ z.val = 1 := inv_eq_one.mp hc.symm
    have hzZ : (z.val : X ⧸ Q.D) ∈ centralizer (Z : Set _) := by
      have hk : z.val ∈ ρ.ker := hρ
      rwa [RootAction.action_kernel] at hk
    exact Subtype.ext (hCfaith z.val z.property hzZ)
  rw [←hCcard]
  exact card_dvd_of_injective f hf

open BenderSuzuki.MatrixGroups BenderSuzuki.External
open BenderSuzuki.ZD.RankOneModelGeometry
open BenderSuzuki.PFAppendixIII

private theorem sylow_of_model_card
    {R M : Type*} [Group R] [Finite R] [Group M] [Finite M] (A : Subgroup R)
    {q : ℕ} (μ : R ≃* M) (hA : IsPGroup 2 A) (hcardA : Nat.card A=q)
    (hc : ∀ T : Sylow 2 M, Nat.card T=q) :
    ∃ S : Sylow 2 R, (S : Subgroup R)=A := by
  obtain ⟨S,hS⟩ := hA.exists_le_sylow
  let S' := S.mapSurjective (f:=μ.toMonoidHom) μ.surjective
  let e : S ≃* S' := (S : Subgroup R).equivMapOfInjective μ.toMonoidHom μ.injective
  have hcardS : Nat.card S=q := (Nat.card_congr e.toEquiv).trans (hc S')
  exact ⟨S,(eq_of_le_of_card_ge hS (by rw [hcardA,hcardS])).symm⟩

private theorem source_unitary_pair (j : Fin 2)
    (hK : simpleRemainder Q split j ≤ localKernel Q j)
    (S : Sylow 2 (rankOne Q split j))
    (hS : (S : Subgroup (rankOne Q split j))=(simpleRoot Q split j).subgroupOf (rankOne Q split j)) :
    let r := involutoryRootReflection Q split j (UnitarySource.actorReflection Q split j)
    let t : rankOne Q split j := ⟨r.val,r.mem_rankOne⟩
    IsInvolution t ∧ t ∉ normalizer (S : Set (rankOne Q split j)) ∧
      twoPoint (normalizer (S : Set (rankOne Q split j))) t =
        (Q.tits.B ⊓ Q.tits.N).subgroupOf (rankOne Q split j) := by
  dsimp only
  let s := UnitarySource.actorReflection Q split j
  let r := involutoryRootReflection Q split j s
  let t : rankOne Q split j := ⟨r.val,r.mem_rankOne⟩
  have ht : IsInvolution t := ⟨fun he => involutoryRootReflection_ne_one Q split j s
    (congrArg Subtype.val he),Subtype.ext (involutoryRootReflection_sq Q split j s)⟩
  have htB : t ∉ normalizer (S : Set (rankOne Q split j)) := by
    intro htB
    rw [show (S : Set (rankOne Q split j))=
      ((simpleRoot Q split j).subgroupOf (rankOne Q split j) : Set _) from congrArg SetLike.coe hS] at htB
    exact Q.tits.representative_not_mem_B (Q.simple_mem j) r.val r.class_eq
      ((rankOne_borel_iff_root_normalizer Q split j hK t).mpr htB)
  refine ⟨ht,htB,?_⟩
  ext x
  change x ∈ normalizer (S : Set (rankOne Q split j)) ∧
    x ∈ BenderSuzuki.PFchapter1section1.rightConjugate (normalizer (S : Set (rankOne Q split j))) t ↔ _
  rw [LinearGeometry.mem_rightConjugate]
  simp only [show (S : Set (rankOne Q split j))=
    ((simpleRoot Q split j).subgroupOf (rankOne Q split j) : Set _) from congrArg SetLike.coe hS,
    ←rankOne_borel_iff_root_normalizer Q split j hK]
  constructor
  · intro hx
    apply UnitarySource.oppositeLevi_inf_two_borels_le_torus Q split j
    refine ⟨UnitarySource.rootActor_le_oppositeLevi Q split j x.property,hx.1,?_⟩
    rw [borelConjugate_eq _ r.val r.class_eq]
    exact hx.2
  · intro hx
    exact ⟨hx.1,((torus_conjugate r.val).symm ▸ hx).1⟩

private theorem source_unitary_inverted_torus
    {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    {b : ℕ} (hb : 2 ≤ b) (hcard : Nat.card E=(2^b)^2)
    (hf : Nat.card {x : E // J.conj x=x}=2^b)
    (j : Fin 2) (hK : simpleRemainder Q split j ≤ localKernel Q j)
    (hroot : Nat.card (simpleRoot Q split j)=(2^b)^3)
    (hmodel : Nonempty (rankOne Q split j ≃* J.specialSubgroup) ∨
      Nonempty (rankOne Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J)) :
    ∃ C : Subgroup ↥(Q.tits.B ⊓ Q.tits.N), IsCyclic C ∧ Nat.card C=2^b-1 ∧
      (∀ z ∈ C, (z : X ⧸ Q.D) ∈ rankOne Q split j) ∧
      (∀ z ∈ C, simpleCartanAction Q split j z=z⁻¹) := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  have hp (T : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)) : Nat.card T=(2^b)^3 := by
    rw [Nat.card_congr (T.equiv (HermitianForm.EvenTwoRank.rootSylow J hJ (by omega) hcard hf)).toEquiv]
    exact HermitianForm.OddPrimeSylow.NormalizedOuter.Coverage.rootGroup_card J hJ _ hcard hf
  have hs (T : Sylow 2 J.specialSubgroup) : Nat.card T=(2^b)^3 :=
    (Nat.card_congr (HermitianForm.SylowOmega.specialSylowEquivProjective J T).toEquiv).trans
      (hp (T.mapSurjective J.specialToProjective_surjective))
  let A := (simpleRoot Q split j).subgroupOf (rankOne Q split j)
  have hA : IsPGroup 2 A := (split.isTwo.to_le (simpleRoot_le Q split j)).comap_subtype
  have hcardA : Nat.card A=(2^b)^3 :=
    (Nat.card_congr (subgroupOfEquivOfLe
      (show simpleRoot Q split j ≤ rankOne Q split j from le_sup_left)).toEquiv).trans hroot
  obtain ⟨S,hS⟩ : ∃ S : Sylow 2 (rankOne Q split j),
      (S : Subgroup (rankOne Q split j))=(simpleRoot Q split j).subgroupOf (rankOne Q split j) := by
    rcases hmodel with ⟨⟨μ⟩⟩ | ⟨⟨μ⟩⟩
    · exact sylow_of_model_card A μ hA hcardA hs
    · exact sylow_of_model_card A μ hA hcardA hp
  let r := involutoryRootReflection Q split j (UnitarySource.actorReflection Q split j)
  let t : rankOne Q split j := ⟨r.val,r.mem_rankOne⟩
  obtain ⟨ht,htB,hD⟩ := source_unitary_pair Q split j hK S hS
  let D := (Q.tits.B ⊓ Q.tits.N).subgroupOf (rankOne Q split j)
  let T := ⁅D,zpowers t⁆
  have hT : IsCyclic T ∧ Nat.card T=2^b-1 ∧ ∀ z ∈ T, rightConjugateElem z t=z⁻¹ := by
    rcases hmodel with ⟨⟨μ⟩⟩ | ⟨⟨μ⟩⟩
    · have hh := unitary_special_tori_of_equiv J hb hJ hcard hf μ S t ht htB
      rw [hD] at hh
      exact ⟨hh.2.2.1,hh.2.2.2.1,hh.2.2.2.2.1⟩
    · have hh := unitary_projective_tori_of_equiv J hb hJ hcard hf μ S t ht htB
      rw [hD] at hh
      exact ⟨hh.2.2.1,hh.2.2.2.1,hh.2.2.2.2.1⟩
  have htD : t ∈ normalizer (D : Set (rankOne Q split j)) := by
    apply mem_normalizer_iff.mpr
    intro x
    exact mem_normalizer_iff.mp (torus_normalizes r.val) (x : X ⧸ Q.D)
  have hTD : T ≤ D := le_normalizer_iff_commutator_le_left.mp (zpowers_le.mpr htD)
  let f : T →* ↥(Q.tits.B ⊓ Q.tits.N) := {
    toFun z := ⟨z.val,hTD z.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hinj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : ↥(Q.tits.B ⊓ Q.tits.N) => (z : X ⧸ Q.D)) hxy
  let := hT.1
  refine ⟨f.range,(MonoidHom.ofInjective hinj).isCyclic.mp inferInstance,
    (Nat.card_congr (MonoidHom.ofInjective hinj).symm.toEquiv).trans hT.2.1,?_,?_⟩
  · rintro _ ⟨z,rfl⟩
    exact z.val.property
  · rintro _ ⟨z,rfl⟩
    apply Subtype.ext
    rw [simpleCartanAction_apply Q split j r.val r.class_eq]
    exact congrArg Subtype.val (hT.2.2 z.val z.property)

private theorem subgroup_faithful_of_prime_fixedFree
    {M : Type*} [Group M] [Finite M] (C A : Subgroup M) (hA : A ≠ ⊥)
    (hfixed : ∀ p : ℕ, p.Prime → p ∣ Nat.card C → ∀ t : M, orderOf t=p →
      A ⊓ centralizer ({t} : Set M)=⊥) : C ⊓ centralizer (A : Set M)=⊥ := by
  by_contra hne
  let K := C ⊓ centralizer (A : Set M)
  obtain ⟨p,hp,hd⟩ := Nat.exists_prime_and_dvd (fun hh => hne (K.card_eq_one.mp hh))
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨t,ht⟩ := exists_prime_orderOf_dvd_card' (G:=K) p hd
  have hf := hfixed p hp (hd.trans (card_dvd_of_le (show K ≤ C from inf_le_left)))
    t ((Subgroup.orderOf_coe t).trans ht)
  apply hA
  apply bot_unique
  intro a ha
  apply (show A ⊓ centralizer ({(t : M)} : Set M) ≤ ⊥ from hf.le)
  exact ⟨ha,mem_centralizer_singleton_iff.mpr
    ((mem_centralizer_iff.mp t.property.2 a ha))⟩

private theorem unitary_prime_fixedFree_of_model
    {E M : Type*} [Field E] [Finite E] [Group M] [Finite M] (J : HermitianForm 3 E)
    {b p : ℕ} (hb : 2 ≤ b) (hcard : Nat.card E=(2^b)^2)
    (hconj : ∀ x, J.conj x=x^(2^b)) (hp : p.Prime) (hd : p ∣ 2^b-1)
    (hmodel : Nonempty (M ≃* J.specialSubgroup) ∨
      Nonempty (M ≃* ProjectiveSpecialUnitaryMatrixGroup J))
    (A : Subgroup M) (hA : IsPGroup 2 A) (t : M) (ht : orderOf t=p) :
    A ⊓ centralizer ({t} : Set M)=⊥ := by
  have applyMap (f : M →* ProjectiveSpecialUnitaryMatrixGroup J)
      (hinj : ∀ a ∈ A, f a=1 → a=1) (htf : orderOf (f t)=p) :
      A ⊓ centralizer ({t} : Set M)=⊥ := by
    have hh := unitary_prime_two_centralizer J hb hcard hconj hp hd (A.map f) (hA.map f) (f t) htf
    apply eq_bot_iff.mpr
    intro a ha
    apply mem_bot.mpr
    apply hinj a ha.1
    apply mem_bot.mp
    rw [←hh]
    exact ⟨mem_map_of_mem _ ha.1,mem_centralizer_singleton_iff.mpr
      (by simpa only [map_mul] using congrArg f (mem_centralizer_singleton_iff.mp ha.2))⟩
  rcases hmodel with ⟨⟨μ⟩⟩ | ⟨⟨μ⟩⟩
  · let f := J.specialToProjective.comp μ.toMonoidHom
    have hk3 : IsPGroup 3 J.specialToProjective.ker :=
      fun x => ⟨1,by simpa using J.specialToProjective_ker_cube x⟩
    have hdis := (hA.map μ.toMonoidHom).disjoint_of_coprime hk3 (by decide : Nat.Coprime 2 3)
    apply applyMap f
    · intro a ha hz
      exact μ.map_eq_one_iff.mp (disjoint_def.mp hdis (mem_map_of_mem _ ha) hz)
    · exact special_unitary_prime_projection_order J hconj hp hd (μ t) ((μ.orderOf_eq t).trans ht)
  · exact applyMap μ.toMonoidHom (fun _ _ hh => μ.map_eq_one_iff.mp hh) ((μ.orderOf_eq t).trans ht)

private theorem source_unitary_torus_faithful
    {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
    {b : ℕ} (hb : 2 ≤ b) (hcard : Nat.card E=(2^b)^2)
    (hconj : ∀ x, J.conj x=x^(2^b))
    (j : Fin 2)
    (hmodel : Nonempty (rankOne Q split j ≃* J.specialSubgroup) ∨
      Nonempty (rankOne Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J))
    (Z : Subgroup (X ⧸ Q.D)) (hZ : Z ≤ simpleRoot Q split j) (hZne : Z ≠ ⊥)
    (C : Subgroup ↥(Q.tits.B ⊓ Q.tits.N)) (hCcard : Nat.card C=2^b-1)
    (hC : ∀ z ∈ C, (z : X ⧸ Q.D) ∈ rankOne Q split j) :
    ∀ z ∈ C, (z : X ⧸ Q.D) ∈ centralizer (Z : Set _) → z=1 := by
  let A := Z.subgroupOf (rankOne Q split j)
  have hZle : Z ≤ rankOne Q split j := hZ.trans le_sup_left
  have hA : IsPGroup 2 A := ((split.isTwo.to_le (simpleRoot_le Q split j)).to_le hZ).comap_subtype
  let f : C →* rankOne Q split j := {
    toFun z := ⟨z.val,hC z.val z.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hinj : Function.Injective f := by
    intro x y hh
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : rankOne Q split j => (z : X ⧸ Q.D)) hh
  have hAne : A ≠ ⊥ := by
    intro he
    apply hZne
    apply bot_unique
    intro z hz
    have hh : (⟨z,hZle hz⟩ : rankOne Q split j) ∈ A := hz
    rw [he] at hh
    exact mem_bot.mpr (congrArg Subtype.val (mem_bot.mp hh))
  have hcentral := subgroup_faithful_of_prime_fixedFree f.range A hAne (by
    intro p hp hd t ht
    have hc : Nat.card f.range=2^b-1 :=
      (Nat.card_congr (MonoidHom.ofInjective hinj).symm.toEquiv).trans hCcard
    rw [hc] at hd
    exact unitary_prime_fixedFree_of_model J hb hcard hconj hp hd hmodel A hA t ht)
  intro z hz hzc
  have hh : f ⟨z,hz⟩ ∈ f.range ⊓ centralizer (A : Set (rankOne Q split j)) := by
    refine ⟨⟨⟨z,hz⟩,rfl⟩,?_⟩
    apply mem_centralizer_iff.mpr
    intro a ha
    exact Subtype.ext (mem_centralizer_iff.mp hzc a ha)
  rw [hcentral] at hh
  apply Subtype.ext
  exact congrArg (fun y : rankOne Q split j => (y : X ⧸ Q.D)) (mem_bot.mp hh)

open BenderSuzuki.MatrixGroups.HermitianForm
open BorelTorus BorelTorus.EvenCenterAction

private theorem source_unitary_center_data
    {E : Type*} [Field E] [Finite E] [CharP E 2] (J : HermitianForm 3 E)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    {b : ℕ} (hb : 0 < b) (hcard : Nat.card E=(2^b)^2)
    (hf : Nat.card {x : E // J.conj x=x}=2^b)
    (j : Fin 2) (hK : simpleRemainder Q split j ≤ localKernel Q j)
    (μ : localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J) :
    let Z := (center (simpleRoot Q split j)).map (simpleRoot Q split j).subtype
    IsElementaryAbelian 2 Z ∧ Nat.card Z=2^b := by
  let U := simpleRoot Q split j
  let Z := (center U).map U.subtype
  let e := QuadrangleStructure.simpleRootUnitaryEquiv J Q split hb hcard hf hJ j hK μ
  let c : center (hermitianUnipotentCoord J) ≃* Multiplicative (fixedField J) :=
    (MulEquiv.subgroupCongr (QuadrangleStructure.binary_coord_center J hb hcard hf)).trans
      (MonoidHom.ofInjective (centralCoord_injective J)).symm
  let z : Z ≃* Multiplicative (fixedField J) :=
    ((center U).equivMapOfInjective U.subtype U.subtype_injective).symm.trans
      ((Subgroup.centerCongr e).trans c)
  let : IsElementaryAbelian 2 (Multiplicative (fixedField J)) := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => by
      apply Multiplicative.toAdd.injective
      change (2 : ℕ) • x.toAdd=0
      rw [two_nsmul]
      exact CharTwo.add_self_eq_zero _) }
  exact ⟨IsElementaryAbelian.of_injective z.toMonoidHom z.injective,
    (Nat.card_congr z.toEquiv).trans ((Nat.card_congr Multiplicative.toAdd).trans hf)⟩

/-- The unitary center torus embeds in the opposite panel Cartan when its binary degree is odd. -/
theorem unitary_center_dvd_opposite
    {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
    {b : ℕ} (hb : 2 ≤ b) (hob : Odd b) (hcard : Nat.card E=(2^b)^2)
    (hconj : ∀ x, J.conj x=x^(2^b))
    (hm : rotationOrder Q=8) (i j : Fin 2) (hij : i ≠ j)
    (hK : simpleRemainder Q split j ≤ localKernel Q j)
    (hroot : Nat.card (simpleRoot Q split j)=(2^b)^3)
    (μ : localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (hmodel : Nonempty (rankOne Q split j ≃* J.specialSubgroup) ∨
      Nonempty (rankOne Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J)) :
    2^b-1 ∣ Nat.card (cartanPanelMap Q i).range := by
  have hf := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 b (by omega) hcard hconj
  let : Fintype E := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow (p:=2) (f:=b*2)
    (by simpa only [pow_mul,Nat.card_eq_fintype_card] using hcard)
  let J₀ := OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J
  obtain ⟨M,hM⟩ := OddPrimeSylow.NormalizedOuter.FormTransport.exists_standard_basis J (2^b) hcard hf
  let es := OddPrimeSylow.NormalizedOuter.FormTransport.specialEquiv J M hM
  let ep := OddPrimeSylow.NormalizedOuter.FormTransport.projectiveEquiv J M hM
  have hmodel₀ : Nonempty (rankOne Q split j ≃* J₀.specialSubgroup) ∨
      Nonempty (rankOne Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J₀) := by
    rcases hmodel with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · exact Or.inl ⟨e.trans es⟩
    · exact Or.inr ⟨e.trans ep⟩
  obtain ⟨C,hcyc,hCcard,hCrank,hCinv⟩ :=
    source_unitary_inverted_torus Q split J₀ rfl hb hcard hf j hK hroot hmodel₀
  let Z := (center (simpleRoot Q split j)).map (simpleRoot Q split j).subtype
  have hZle : Z ≤ simpleRoot Q split j := map_subtype_le _
  obtain ⟨hZE,hZcard⟩ := source_unitary_center_data Q split J₀ rfl hob.pos hcard hf j hK (μ.trans ep)
  have hZne : Z ≠ ⊥ := by
    intro he
    have hh : Nat.card Z=1 := Z.card_eq_one.mpr he
    rw [hZcard] at hh
    exact (ne_of_gt (Nat.one_lt_two_pow hob.pos.ne')) hh
  let := hcyc
  let := hZE
  exact center_torus_dvd_panel Q split hm i j hij hob Z rfl hZcard C hCcard hCinv
    (source_unitary_torus_faithful Q split J hb hcard hconj j hmodel Z hZle hZne C hCcard hCrank)
    (UnitarySource.actorReflection Q split)

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure
