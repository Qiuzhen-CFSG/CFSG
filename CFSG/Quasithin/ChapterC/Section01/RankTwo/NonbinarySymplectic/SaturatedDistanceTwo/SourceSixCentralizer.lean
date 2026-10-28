module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceSixDisplacement
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceThreeGenerators
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The whole-core contradiction in MS93 (3.7)(6)

The fixed layer X = C_{Z′}(x^g) projects to a field hyperplane containing
the plane fixed by the full midpoint radical. Choose one vector of that
hyperplane outside the fixed plane. Evaluation on this vector is a
homomorphism from any subgroup of the radical into its natural displacement.
Its kernel centralizes the whole original X: field linearity controls the
hyperplane, fixed-vector lifting controls the full cover, and the midpoint
omega-center supplies the full central supplement.

The displacement index proved in SourceSixDisplacement therefore bounds
[Q′^g : C_{Q′^g}(X)] by q. The natural fixed index gives the reverse bound.
The resulting source selection retains the same x, conjugator and induced
midpoint action, the original maps and the entire fixed attachments.

Four conjugates of the resulting root subgroup generate the component.
Their fixed-codimension bound forces the whole core to be its moving layer
times its full fixed core. Paired attachment equality puts this fixed core
in the opposite core. Regularity then puts the commuting conjugate there
as well, contradicting its selection. Thus a genuine critical pair of
order q exists; source (3) now gives the whole-core decomposition everywhere.

This is the whole-core contradiction on printed p.876 of Meierfrankenfeld--
Stellmacher, Pushing up weak BN-pairs of rank two (1993), (3.7)(6).
Attachment triviality and the field-four endgame remain subsequent source
steps. The Chapter11 consumers use their literal intrinsic MS quotient.
-/

public noncomputable section
open scoped IsMulCommutative commutatorElement
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.OneCohomology Representation.SymplecticFourOrthogonalCover
open Theory.SpecificGroups.SymplecticFour

private theorem hyperplane_spanned_by_plane_vector
    {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (P D : Submodule F V) (hPD : P ≤ D)
    (hP : Module.finrank F P=2) (hD : Module.finrank F D=3)
    (v : V) (hvD : v ∈ D) (hvP : v ∉ P) :
    D=P ⊔ Submodule.span F {v} := by
  symm
  apply Submodule.eq_of_le_of_finrank_eq
  · exact sup_le hPD (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hvD))
  · rw [Submodule.finrank_sup_span_singleton hvP,hP,hD]

private theorem cover_hyperplane_centralizer_bound
    {F W G : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W] [Group G]
    (σ : Representation (ZMod 2) (L (K := F)) W)
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (U T B X C : Subgroup G) [Finite B]
    (hBT : B ≤ T) (hTU : T ≤ normalizer (U : Set G))
    (j : Multiplicative W →* G) (hj : Function.Injective j) (hjr : j.range=U)
    (β : T →* L (K := F))
    (hact : ∀ t : T, ∀ w : W, j (Multiplicative.ofAdd (σ (β t) w))=
      t.val*j (Multiplicative.ofAdd w)*t.val⁻¹)
    (P D : Submodule F (Vector F)) (hPD : P ≤ D)
    (hP : Module.finrank F P=2) (hD : Module.finrank F D=3)
    (hfix : ∀ t : T, ∀ v ∈ P, (β t).val • v=v)
    (hmove : ∀ t : T, ∀ v : Vector F, (β t).val • v-v ∈ P)
    (hX : ∀ w : W, j (Multiplicative.ofAdd w) ∈ X ↔ p w ∈ D)
    (hXC : X=(X ⊓ U) ⊔ C) (hCT : C ≤ centralizer (T : Set G))
    (hCU : C ≤ centralizer (U : Set G)) :
    (centralizer (X : Set G)).relIndex B ≤
      (p.toLinearMap.ker.toAddSubgroup.toSubgroup.map j).relIndex ⁅B,X⁆ := by
  let A := p.toLinearMap.ker.toAddSubgroup.toSubgroup.map j
  have hCnorm : C ≤ normalizer ((X ⊓ U : Subgroup G) : Set G) :=
    (hCU.trans (centralizer_le inf_le_right)).trans (Subgroup.centralizer_le_normalizer _)
  have hMU : ⁅B,X⁆ ≤ U := by
    apply commutator_le.mpr
    intro b hb x hx
    rw [hXC,←SetLike.mem_coe,coe_mul_of_right_le_normalizer_left _ _ hCnorm] at hx
    obtain ⟨u,hu,c,hc,rfl⟩ := hx
    have hbc : Commute b c := hCT hc b (hBT hb)
    rw [commutatorElement_mul_right_eq_mul_conj,commutatorElement_eq_one_iff_commute.mpr hbc]
    simpa only [mul_one,mul_inv_cancel_right] using
      (le_normalizer_iff_commutator_le_right.mp hTU) (commutator_mem_commutator (hBT hb) hu.2)
  obtain ⟨π,hπ,hπj,hπact⟩ := exists_equivariant_embedded_projection U T hTU σ
    (binaryNatural (K := F)) j hj hjr p.toLinearMap hp.1
    (fun t w => LinearMap.congr_fun (p.isIntertwining' t) w) β hact
  have hk : π.ker.map U.subtype=A := by
    apply le_antisymm
    · rintro x ⟨u,hu,rfl⟩
      obtain ⟨w,hw⟩ := (hjr.symm ▸ u.property : u.val ∈ j.range)
      have he : u=⟨j w,by rw [←hjr]; exact ⟨w,rfl⟩⟩ := Subtype.ext hw.symm
      refine ⟨w,?_,hw⟩
      have hh : π u=1 := hu
      rw [he] at hh
      exact congrArg Multiplicative.toAdd ((hπj w.toAdd).symm.trans hh)
    · rintro x ⟨w,hw,rfl⟩
      refine ⟨⟨j w,by rw [←hjr]; exact ⟨w,rfl⟩⟩,?_,rfl⟩
      exact (hπj w.toAdd).trans (congrArg Multiplicative.ofAdd hw)
  have hnot : ¬ D ≤ P := by
    intro hh
    have hd := Submodule.finrank_mono hh
    rw [hD,hP] at hd
    omega
  obtain ⟨v,hvD,hvP⟩ := Set.not_subset.mp hnot
  obtain ⟨w,hw⟩ := hp.1 v
  have hwX : j (Multiplicative.ofAdd w) ∈ X := (hX w).mpr (hw ▸ hvD)
  have hspan := hyperplane_spanned_by_plane_vector P D hPD hP hD v hvD hvP
  let f : B →* Multiplicative (Vector F) :=
    { toFun := fun b => Multiplicative.ofAdd ((β (inclusion hBT b)).val • v-v)
      map_one' := by simp
      map_mul' := by
        intro b c
        apply Multiplicative.toAdd.injective
        change (β (inclusion hBT (b*c))).val • v-v=
          ((β (inclusion hBT b)).val • v-v)+((β (inclusion hBT c)).val • v-v)
        rw [map_mul,map_mul]
        change ((β (inclusion hBT b)).val*(β (inclusion hBT c)).val) • v-v=_
        rw [mul_smul]
        have hh := hfix (inclusion hBT b) _ (hmove (inclusion hBT c) v)
        rw [smul_sub] at hh
        linear_combination hh }
  have hkernel : f.ker=(centralizer (X : Set G)).subgroupOf B := by
    ext b
    change (β (inclusion hBT b)).val • v-v=0 ↔ b.val ∈ centralizer (X : Set G)
    rw [sub_eq_zero]
    constructor
    · intro hb
      have hDfix : ∀ u ∈ D, (β (inclusion hBT b)).val • u=u := by
        intro u hu
        rw [hspan] at hu
        obtain ⟨r,hr,s,hs,rfl⟩ := Submodule.mem_sup.mp hu
        obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hs
        rw [smul_add,hfix (inclusion hBT b) r hr,smul_comm,hb]
      have hc : b.val ∈ centralizer ((X ⊓ U : Subgroup G) : Set G) := by
        intro u hu
        obtain ⟨w',rfl⟩ := (hjr.symm ▸ hu.2 : u ∈ j.range)
        have hh := cover_fixed_of_projection_fixed p hp (β (inclusion hBT b)) w'.toAdd
          (hDfix _ ((hX w'.toAdd).mp hu.1))
        have he := congrArg (fun z => j (Multiplicative.ofAdd z)) hh
        rw [hact,ofAdd_toAdd,mul_inv_eq_iff_eq_mul] at he
        exact he.symm
      intro u hu
      rw [hXC,coe_mul_of_right_le_normalizer_left _ _ hCnorm] at hu
      obtain ⟨r,hr,s,hs,rfl⟩ := hu
      have hscomm : Commute b.val s := hCT hs b.val (hBT b.property)
      calc
        (r*s)*b.val=r*(b.val*s) := by rw [mul_assoc,hscomm.eq]
        _ = b.val*(r*s) := by rw [←mul_assoc,hc r hr,mul_assoc]
    · intro hb
      have hh : σ (β (inclusion hBT b)) w=w := by
        apply Multiplicative.ofAdd.injective
        apply hj
        rw [hact]
        change b.val*j (Multiplicative.ofAdd w)*b.val⁻¹=_
        rw [←hb _ hwX,mul_inv_cancel_right]
      have he := congrArg p hh
      rw [p.isIntertwining,hw] at he
      exact he
  have hr : f.range ≤ (⁅B,X⁆.subgroupOf U).map π := by
    rintro _ ⟨b,rfl⟩
    let u : U := ⟨j (Multiplicative.ofAdd w),by rw [←hjr]; exact ⟨_,rfl⟩⟩
    let z : U := ⟨b.val*u.val*b.val⁻¹,
      (mem_normalizer_iff.mp (hTU (hBT b.property)) u.val).mp u.property⟩*u⁻¹
    refine ⟨z,commutator_mem_commutator b.property hwX,?_⟩
    dsimp only [z]
    rw [map_mul,map_inv]
    have he := hπact (inclusion hBT b) u
    change π ⟨b.val*u.val*b.val⁻¹,_⟩ =
      Multiplicative.ofAdd (binaryNatural (β (inclusion hBT b)) (π u).toAdd) at he
    rw [he]
    have hpw : π u=Multiplicative.ofAdd v := (hπj w).trans (congrArg Multiplicative.ofAdd hw)
    rw [hpw]
    apply Multiplicative.toAdd.injective
    change (β (inclusion hBT b)).val • v + -v=(β (inclusion hBT b)).val • v-v
    exact (sub_eq_add_neg _ _).symm
  have hi : A.relIndex ⁅B,X⁆=Nat.card ((⁅B,X⁆.subgroupOf U).map π) := by
    rw [←relIndex_ker]
    have hh := relIndex_subgroupOf (H := A) hMU
    rw [←hk,subgroupOf_map_subtype_eq] at hh
    rw [hk] at hh
    exact hh.symm
  calc
    _ = f.ker.index := by rw [hkernel]; rfl
    _ = Nat.card f.range := index_ker f
    _ ≤ Nat.card ((⁅B,X⁆.subgroupOf U).map π) :=
      Nat.card_le_card_of_injective (inclusion hr) (inclusion_injective _)
    _ = _ := hi.symm

private theorem conjugate_plane_geometry
    {F : Type*} [Field F] [CharP F 2]
    (T : Subgroup (Sp F)) (k : Sp F)
    (hk : T.map (MulAut.conj k).toMonoidHom=planeRadicalAmbient) :
    ∃ P : Submodule F (Vector F), Module.finrank F P=2 ∧
      (∀ t ∈ T, ∀ v ∈ P, t • v=v) ∧
      (∀ t ∈ T, ∀ v : Vector F, t • v-v ∈ P) := by
  let P := (plane F).map (toLinear k⁻¹).toLinearMap
  refine ⟨P,((toLinear k⁻¹).finrank_map_eq _).trans finrank_plane,?_,?_⟩
  · intro t ht v hv
    obtain ⟨w,hw,rfl⟩ := hv
    have ht' : k*t*k⁻¹ ∈ planeRadicalAmbient := hk ▸ mem_map_of_mem _ ht
    obtain ⟨B,hB⟩ := (SymplecticConjugatePair.mem_planeRadical_iff _).mp ht'
    have hf : (k*t*k⁻¹) • w=w := by
      rw [←hB]
      ext i
      cases i with
      | inl i => fin_cases i <;> simp [Plane.shearSp,Matrix.mulVec,dotProduct,
          Fintype.sum_sum_type,Fin.sum_univ_two,Matrix.fromBlocks,hw 0,hw 1]
      | inr i => fin_cases i <;> simp [Plane.shearSp,Matrix.mulVec,dotProduct,
          Fintype.sum_sum_type,Fin.sum_univ_two,Matrix.fromBlocks,hw 0,hw 1]
    have hh := congrArg (fun v => k⁻¹ • v) hf
    change t • (k⁻¹ • w)=k⁻¹ • w
    simpa only [mul_smul,inv_smul_smul] using hh
  · intro t ht v
    refine ⟨k • (t • v-v),?_,by change k⁻¹ • (k • (t • v-v))=t • v-v; exact inv_smul_smul _ _⟩
    have ht' : k*t*k⁻¹ ∈ planeRadicalAmbient := hk ▸ mem_map_of_mem _ ht
    obtain ⟨B,hB⟩ := (SymplecticConjugatePair.mem_planeRadical_iff _).mp ht'
    have he : k • (t • v-v)=(Plane.shearSp B) • (k • v)-k • v := by
      rw [hB,mul_smul,mul_smul,inv_smul_smul,smul_sub]
    rw [he]
    intro i
    fin_cases i <;> simp [Plane.shearSp,Matrix.mulVec,dotProduct,
      Fintype.sum_sum_type,Fin.sum_univ_two,Matrix.fromBlocks]

private theorem fixed_hyperplane_bound
    {F W G : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W] [Group G]
    (σ : Representation (ZMod 2) (L (K := F)) W)
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (U Z C T Y B A : Subgroup G) [Finite B] [IsMulCommutative Z]
    (hUZ : U ≤ Z) (hCZ : C ≤ Z) (hZ : Z=U ⊔ C)
    (hCT : C ≤ centralizer (T : Set G))
    (hY : Y ≤ T) (hB : B ≤ T) (hTU : T ≤ normalizer (U : Set G))
    (j : Multiplicative W →* G) (hj : Function.Injective j) (hjr : j.range=U)
    (β : T →* L (K := F))
    (hact : ∀ t : T, ∀ w : W, j (Multiplicative.ofAdd (σ (β t) w))=
      t.val*j (Multiplicative.ofAdd w)*t.val⁻¹)
    (k : Sp F) (hk : ((commutator (Sp F)).subtype.comp β).range.map
      (MulAut.conj k).toMonoidHom=planeRadicalAmbient)
    (hdim : Module.finrank F (displacementSpace
      (((commutator (Sp F)).subtype.comp β).comp (inclusion hY)).range)=1)
    (hker : ∀ w : W, p w=0 ↔ j (Multiplicative.ofAdd w) ∈ A) :
    (centralizer ((Z ⊓ centralizer (Y : Set G)) : Set G)).relIndex B ≤
      A.relIndex ⁅B,Z ⊓ centralizer (Y : Set G)⁆ := by
  let α := (commutator (Sp F)).subtype.comp β
  let αY := α.comp (inclusion hY)
  let X := Z ⊓ centralizer (Y : Set G)
  let D := TwoLocalCover.fixedSpace αY.range
  obtain ⟨P,hP,hfix,hmove⟩ := conjugate_plane_geometry α.range k hk
  have hPD : P ≤ D := by
    intro v hv b hb
    obtain ⟨y,rfl⟩ := hb
    exact hfix (α (inclusion hY y)) ⟨_,rfl⟩ v hv
  have hD : Module.finrank F D=3 := by
    change Module.finrank F (TwoLocalCover.fixedSpace αY.range)=3
    rw [←orthogonal_displacementSpace,LinearMap.BilinForm.finrank_orthogonal
      TwoLocalCover.form_nondegenerate,hdim]
    simp [Theory.SpecificGroups.SymplecticFour.Vector]
  have hX (w : W) : j (Multiplicative.ofAdd w) ∈ X ↔ p w ∈ D := by
    have hu : j (Multiplicative.ofAdd w) ∈ U := hjr ▸ ⟨_,rfl⟩
    constructor
    · intro hx b hb
      obtain ⟨y,rfl⟩ := hb
      have he : σ (β (inclusion hY y)) w=w := by
        apply Multiplicative.ofAdd.injective
        apply hj
        rw [hact]
        change y.val*j (Multiplicative.ofAdd w)*y.val⁻¹=_
        rw [hx.2 y.val y.property,mul_inv_cancel_right]
      have hh := congrArg p he
      rw [p.isIntertwining] at hh
      exact hh
    · intro hv
      refine ⟨hUZ hu,?_⟩
      intro y hy
      have he := cover_fixed_of_projection_fixed p hp (β (inclusion hY ⟨y,hy⟩)) w
        (hv (αY ⟨y,hy⟩) ⟨_,rfl⟩)
      have hh := congrArg (fun u => j (Multiplicative.ofAdd u)) he
      rw [hact,mul_inv_eq_iff_eq_mul] at hh
      exact hh
  have hCU : C ≤ centralizer (U : Set G) :=
    hCZ.trans (Z.le_centralizer.trans (centralizer_le hUZ))
  have hXC : X=(X ⊓ U) ⊔ C := by
    apply le_antisymm
    · intro x hx
      have hxz : x ∈ Z := hx.1
      rw [hZ,←SetLike.mem_coe,
        coe_mul_of_right_le_normalizer_left _ _ (hCU.trans (Subgroup.centralizer_le_normalizer _))] at hxz
      obtain ⟨u,hu,v,hv,rfl⟩ := hxz
      have hvC := (hCT.trans (centralizer_le hY)) hv
      have huC : u ∈ centralizer (Y : Set G) := by
        have hh := (centralizer (Y : Set G)).mul_mem hx.2
          ((centralizer (Y : Set G)).inv_mem hvC)
        simpa only [mul_inv_cancel_right] using hh
      exact mul_mem (mem_sup_left ⟨⟨hUZ hu,huC⟩,hu⟩) (mem_sup_right hv)
    · exact sup_le inf_le_left (le_inf hCZ (hCT.trans (centralizer_le hY)))
  have hbound := cover_hyperplane_centralizer_bound σ p hp U T B X C hB hTU j hj hjr β
    hact P D hPD hP hD (fun b => hfix _ ⟨b,rfl⟩)
    (fun b => hmove _ ⟨b,rfl⟩) hX hXC hCT hCU
  have hkproj : p.toLinearMap.ker.toAddSubgroup.toSubgroup.map j=A ⊓ U := by
    apply le_antisymm
    · rintro v ⟨w,hw,rfl⟩
      exact ⟨(hker _).mp hw,hjr ▸ ⟨w,rfl⟩⟩
    · rintro v ⟨hc,hv⟩
      obtain ⟨w,rfl⟩ := hjr.symm ▸ hv
      exact ⟨w,(hker _).mpr hc,rfl⟩
  have hMU : ⁅B,X⁆ ≤ U := by
    apply commutator_le.mpr
    intro b hb x hx
    rw [hXC,←SetLike.mem_coe,coe_mul_of_right_le_normalizer_left _ _
      ((hCU.trans (centralizer_le inf_le_right)).trans (Subgroup.centralizer_le_normalizer _))] at hx
    obtain ⟨u,hu,c,hc,rfl⟩ := hx
    have hbc : Commute b c := hCT hc b (hB hb)
    rw [commutatorElement_mul_right_eq_mul_conj,commutatorElement_eq_one_iff_commute.mpr hbc]
    simpa only [mul_one,mul_inv_cancel_right] using
      (le_normalizer_iff_commutator_le_right.mp hTU) (commutator_mem_commutator (hB hb) hu.2)
  rw [hkproj,←inf_relIndex_right (A ⊓ U) _,inf_assoc,inf_eq_right.mpr hMU,inf_relIndex_right] at hbound
  exact hbound

open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
open DistanceTwoRecognition ChapterB.QuasisimpleSource
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- Evaluation on the full fixed hyperplane bounds an arbitrary subgroup of
its radical. The denominator retains the complete cover attachment. -/
theorem plane_cover_hyperplane_centralizer_bound
    (g : Geometry d.radical) (hb : g.b d.radical=2)
    {z t : Vertex d.radical} (hz : color d.radical z=false)
    (hzt : Adjacent d.radical z t)
    (cv : RadicalPlaneCover d.radical (replacementMovedSection h d) n z t)
    (Y B : Subgroup (FreeAmalgam d.radical)) (hY : Y ≤ Q d.radical t) (hB : B ≤ Q d.radical t)
    (hi : (centralizer (Y : Set (FreeAmalgam d.radical))).relIndex (Z d.radical z)=2^n) :
    (centralizer ((Z d.radical z ⊓ centralizer (Y : Set (FreeAmalgam d.radical))) :
      Set (FreeAmalgam d.radical))).relIndex B ≤
        (U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))).relIndex
          ⁅B,Z d.radical z ⊓ centralizer (Y : Set (FreeAmalgam d.radical))⁆ := by
  have hm := plane_cover_full_fixed_index h d g hb hz hzt cv Y hY
  have hdim : Module.finrank cv.field.Carrier (displacementSpace
      (((commutator (Sp cv.field.Carrier)).subtype.comp cv.actor).comp (inclusion hY)).range)=1 :=
    Nat.pow_right_injective
      (one_lt_pow₀ (by decide : 1<(2:ℕ)) (by have := h.nonbinary; omega))
      (hm.symm.trans (hi.trans (pow_one _).symm))
  have ht : color d.radical t=true := by
    apply Bool.eq_true_of_not_eq_false
    intro he
    exact adjacent_color_ne d.radical hzt (hz.trans he.symm)
  have hCT : Z d.radical t ≤ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) := by
    rw [show Z d.radical t=omegaCenter (Q d.radical t) by simp [Z,ht,edgeOmega]]
    exact fun _ hx => (mem_omegaCenter_iff.mp hx).2.2
  let := g.Z_elementary (by omega) z hz
  let := finite_stabilizer d.radical z
  let : Finite B := Finite.of_injective (inclusion (hB.trans cv.edge_le)) (inclusion_injective _)
  obtain ⟨k,hk⟩ := cv.plane_image
  exact fixed_hyperplane_bound
    (MovedSection.coverAction (replacementMovedSection h d) cv.equiv)
    (MovedSection.coverProjection (replacementMovedSection h d) cv.equiv) cv.cover
    (U d.radical z) (Z d.radical z) (Z d.radical t) (Q d.radical t) Y B
    (U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical)))
    (U_le_Z z) (Sp4Four.edge_Z_le_endpoint d.radical hz hzt)
    (Z_eq_moving_sup_edge_of_distance_two h d g hb hz hzt) hCT hY hB
    (cv.edge_le.trans (U_normalized z)) cv.embedding cv.injective cv.range_eq cv.actor
    cv.actor_conjugation k hk hdim (fun w => (cv.kernel w).trans
      ⟨fun hc => ⟨cv.range_eq ▸ ⟨_,rfl⟩,hc⟩,fun hc => hc.2⟩)

/-- The actual source-(6) selection, now with index q for the centralizer
in the entire moved endpoint core. All selected elements and full attachments
remain those of the preceding construction. -/
theorem source_six_field_pair_or_whole_core_centralizer
    (g : Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hcritical : (2^n)^2 ≤ (Q d.radical z).relIndex (Z d.radical a)) :
    ∃ x ∈ Z d.radical z, x ∉ Q d.radical a ∧
      Z d.radical a ⊓ centralizer ({x} : Set (FreeAmalgam d.radical))=Z d.radical t ∧
      ∃ y ∈ stabilizer d.radical a, ∃ k ∈ stabilizer d.radical t,
        (∀ u ∈ Q d.radical t, (MulAut.conj k) u=(MulAut.conj y) u) ∧
        x⁻¹*(y*x*y⁻¹) ∈ Q d.radical a ∧ Commute x (y*x*y⁻¹) ∧
        y ∉ normalizer (((Z d.radical z ⊔ Q d.radical a) : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) ∧
        Nonempty (CriticalPath d.radical g (act d.radical k⁻¹ z) z) ∧
        ((Q d.radical z).relIndex (Z d.radical (act d.radical k⁻¹ z))=2^n ∨
          (y*x*y⁻¹ ∉ Q d.radical z ∧
            (Z d.radical z ⊓ centralizer ({y*x*y⁻¹} : Set (FreeAmalgam d.radical))).relIndex
              (Z d.radical z)=2^n ∧
            (Q d.radical (act d.radical k⁻¹ z)).relIndex
              (Z d.radical z ⊓ centralizer ({y*x*y⁻¹} : Set (FreeAmalgam d.radical)))=2^n ∧
            (centralizer ((Z d.radical z ⊓ centralizer ({y*x*y⁻¹} : Set (FreeAmalgam d.radical))) :
              Set (FreeAmalgam d.radical))).relIndex (Z d.radical (act d.radical k⁻¹ z))=2^n ∧
            (U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))).relIndex
              ⁅Q d.radical (act d.radical k⁻¹ z),
                Z d.radical z ⊓ centralizer ({y*x*y⁻¹} : Set (FreeAmalgam d.radical))⁆ = 2^n ∧
            ⁅Q d.radical (act d.radical k⁻¹ z),
                Z d.radical z ⊓ centralizer ({y*x*y⁻¹} : Set (FreeAmalgam d.radical))⁆ ⊔
              (U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical))) ≠
                ⁅Z d.radical z,Q d.radical t⁆ ∧
            (centralizer ((Z d.radical z ⊓ centralizer ({y*x*y⁻¹} : Set (FreeAmalgam d.radical))) :
              Set (FreeAmalgam d.radical))).relIndex (Q d.radical (act d.radical k⁻¹ z))=2^n)) := by
  obtain ⟨x,hx,hxQ,hreg,y,hy,k,hk,he,hcoset,hcomm,hmove,⟨p⟩,halt⟩ :=
    source_six_field_pair_or_small_whole_core_movement h d g hb hsat path hat hzt c c' hcritical
  refine ⟨x,hx,hxQ,hreg,y,hy,k,hk,he,hcoset,hcomm,hmove,⟨p⟩,?_⟩
  rcases halt with hsmall | ⟨hwQ,hi,hQi,hCi,hMi,hne⟩
  · exact Or.inl hsmall
  apply Or.inr
  refine ⟨hwQ,hi,hQi,hCi,hMi,hne,?_⟩
  let v := act d.radical k⁻¹ z
  have hkt : act d.radical k⁻¹ t=t := (stabilizer d.radical t).inv_mem hk
  have hvt : Adjacent d.radical v t := by
    simpa only [hkt] using (adjacent_act_iff d.radical k⁻¹ z t).mpr hzt
  obtain ⟨cv⟩ := exists_edgeMarking h d g (by omega) p.start_color hvt
  obtain ⟨_,⟨cz⟩,_⟩ := source_four_large_paired_geometry h d g hb hsat path hat hzt c c' hcritical
  have hZQ (b : Vertex d.radical) (hc : color d.radical b=false) : Z d.radical b ≤ Q d.radical b :=
    (g.omega_bound b hc (by rw [g.distance_constant b hc]; change 0<g.b d.radical; omega)).trans
      (omegaCenter_le _)
  have hxT : x ∈ Q d.radical t := c'.core_le_edge (hZQ z path.end_color hx)
  have hwT : y*x*y⁻¹ ∈ Q d.radical t := by
    have hconj : (MulAut.conj k) x ∈ Q d.radical t :=
      (mem_normalizer_iff.mp (Q_normalized d.radical t hk) x).mp hxT
    rw [he x hxT] at hconj
    exact hconj
  have hcent : centralizer (zpowers (y*x*y⁻¹) : Set (FreeAmalgam d.radical))=
      centralizer ({y*x*y⁻¹} : Set (FreeAmalgam d.radical)) := by
    rw [zpowers_eq_closure,centralizer_closure]
  have hu := plane_cover_hyperplane_centralizer_bound h d g hb path.end_color hzt cz
    (zpowers (y*x*y⁻¹)) (Q d.radical v) (zpowers_le.mpr hwT) cv.core_le_edge
    (by rw [hcent,←inf_relIndex_left]; exact hi)
  rw [hcent,hMi] at hu
  apply le_antisymm hu
  let := finite_stabilizer d.radical v
  let : Finite (Q d.radical v) := Finite.of_injective
    (inclusion (show Q d.radical v ≤ stabilizer d.radical v from fun _ hv => hv.1))
    (inclusion_injective _)
  rw [←hCi]
  exact relIndex_le_of_le_right (hZQ v p.start_color) index_ne_zero_of_finite

private theorem plane_root_generating_conjugates
    (g : Geometry d.radical) (hb : g.b d.radical=2)
    {a t : Vertex d.radical} (ha : color d.radical a=false)
    (hat : Adjacent d.radical a t)
    (cv : RadicalPlaneCover d.radical (replacementMovedSection h d) n a t)
    (B : Subgroup (FreeAmalgam d.radical)) (hBT : B ≤ Q d.radical t)
    (hcard : (Q d.radical a).relIndex B=2^n)
    (hfixed : (centralizer (B : Set (FreeAmalgam d.radical))).relIndex (Z d.radical a)=2^n) :
    ∃ f : Fin 4 → L (K := cv.field.Carrier),
      (⨆ i, (cv.actor.comp (inclusion hBT)).range.map (MulAut.conj (f i)).toMonoidHom)=⊤ := by
  have hm := plane_cover_full_fixed_index h d g hb ha hat cv B hBT
  let E := cv.field
  let e := cv.equiv
  let κ := cv.quotient
  let β := cv.actor
  have hTS := cv.edge_le
  have hαker := cv.actor_kernel
  let k : Sp E.Carrier := Classical.choose cv.plane_image
  have hk := Classical.choose_spec cv.plane_image
  let βB := β.comp (inclusion hBT)
  let α := (commutator (Sp E.Carrier)).subtype.comp β
  let αB := α.comp (inclusion hBT)
  have hEc : Nat.card E.Carrier=2^n := E.card_eq.trans (congrArg (2^·) cv.degree)
  have hq : 1<2^n := one_lt_pow₀ (by decide : 1<(2:ℕ)) (by have := h.nonbinary; omega)
  have hαcard : Nat.card αB.range=2^n := by
    rw [←index_ker,←MonoidHom.comap_ker,hαker,comap_inclusion_subgroupOf]
    exact hcard
  have hβcard : Nat.card βB.range=Nat.card E.Carrier := by
    have hr : αB.range=βB.range.map (commutator (Sp E.Carrier)).subtype :=
      MonoidHom.range_comp (commutator (Sp E.Carrier)).subtype βB
    rw [hr,card_map_of_injective (commutator (Sp E.Carrier)).subtype_injective] at hαcard
    exact hαcard.trans hEc.symm
  have hdim : Module.finrank E.Carrier (displacementSpace αB.range)=1 := by
    exact Nat.pow_right_injective hq (hm.symm.trans (hfixed.trans (pow_one _).symm))
  have hαmap : βB.range.map (commutator (Sp E.Carrier)).subtype=αB.range :=
    (MonoidHom.range_comp (commutator (Sp E.Carrier)).subtype βB).symm
  let P := Classical.choose (conjugate_plane_geometry (F := E.Carrier) α.range k hk)
  have hfix := (Classical.choose_spec (conjugate_plane_geometry (F := E.Carrier) α.range k hk)).2.1
  have hmove := (Classical.choose_spec (conjugate_plane_geometry (F := E.Carrier) α.range k hk)).2.2
  have hquad : ∀ x ∈ αB.range, ∀ y ∈ αB.range, ∀ v : Vector E.Carrier,
      x • (y • v-v)=y • v-v := by
    rintro _ ⟨x,rfl⟩ _ ⟨y,rfl⟩ v
    exact hfix _ ⟨inclusion hBT x,rfl⟩ _ (hmove _ ⟨inclusion hBT y,rfl⟩ v)
  have hlarge : 2<Nat.card E.Carrier := by
    rw [hEc]
    exact lt_of_lt_of_le (by decide : 2<2^2) (Nat.pow_le_pow_right (by decide) h.nonbinary)
  exact derived_four_conjugates_of_displacement_one (F := E.Carrier) hlarge βB.range hβcard
    (by rw [hαmap]; exact hdim) (by rw [hαmap]; exact hquad)

omit [Group H] [Finite H] [Field F] [Finite F] [CharP F 2] h in
private theorem four_conjugate_finrank_bound
    {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) G V) (B : Subgroup G) (f : Fin 4 → G)
    (hf : (⨆ i, B.map (MulAut.conj (f i)).toMonoidHom)=⊤)
    (hfixed : fixedSpace σ ⊤=⊥) :
    Module.finrank (ZMod 2) V ≤ 4 * fixedCodim σ B := by
  have ht := fixedCodim_le_card_mul_of_subgroup_conjugates σ ⊤ B f hf.ge
  have hd := fixedCodim_add_finrank σ ⊤
  rw [hfixed,finrank_bot,add_zero] at hd
  simpa only [hd,Fintype.card_fin] using ht

omit [Group H] [Finite H] [Field F] [Finite F] [CharP F 2] h in
private theorem whole_core_index_bound_of_conjugates
    {M J G : Type*} [Group M] [Group J] [Group G]
    (T : Subgroup M) (a : Vertex T) (s : WholeKernelQuotient T a J)
    [Finite (Q T a)] (q n : ℕ) (hqn : q=2^n)
    (B : Subgroup (FreeAmalgam T)) (hBS : B ≤ stabilizer T a)
    (hSN : stabilizer T a ≤ normalizer (fixedCore T a : Set (FreeAmalgam T)))
    (γ : G →* J) (A : Subgroup G) (f : Fin 4 → G)
    (hf : (⨆ i, A.map (MulAut.conj (f i)).toMonoidHom)=⊤)
    (hmap : (B.subgroupOf (stabilizer T a)).map s.quotient=A.map γ)
    (hfixed : fixedSpace (s.action.comp γ) ⊤=⊥)
    (hindex : (centralizer (B : Set (FreeAmalgam T))).relIndex (Q T a) ≤ q) :
    (fixedCore T a).relIndex (Q T a) ≤ q^4 := by
  let σ := s.action.comp γ
  have htotal : Module.finrank (ZMod 2) s.Carrier ≤ 4 * fixedCodim σ A :=
    four_conjugate_finrank_bound (V := s.Carrier) σ A f hf hfixed
  have hi := s.sectionData.fixed_index_of_relative_normalizers B hBS
    (s.sectionData.section_le.trans hSN) (hBS.trans hSN)
  unfold fixedCodim at hi
  rw [fixedSpace_comp_map,hmap,←fixedSpace_comp_map] at hi
  change (commutatorPreimage (Q T a) B (fixedCore T a)).relIndex
    (Q T a)=2^fixedCodim σ A at hi
  have hbound : 2^fixedCodim σ A ≤ q := by
    rw [←hi]
    apply le_trans ?_ hindex
    rw [←inf_relIndex_right (centralizer (B : Set (FreeAmalgam T))) (Q T a)]
    apply relIndex_le_of_le_left ?_ index_ne_zero_of_finite
    apply le_commutatorPreimage inf_le_right
    rw [commutator_eq_bot_iff_le_centralizer.mpr inf_le_left]
    exact bot_le
  rw [hqn] at hbound
  have hcodim : fixedCodim σ A ≤ n :=
    (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp hbound
  have horder : (fixedCore T a).relIndex (Q T a)=Nat.card s.Carrier := by
    change ((Q T a ⊓ centralizer (Ltilde T a : Set (FreeAmalgam T))).subgroupOf (Q T a)).index=_
    rw [←s.sectionData.kernel_eq,index_ker,MonoidHom.range_eq_top.mpr s.sectionData.onto,card_top]
    rfl
  have hsmall : (fixedCore T a).relIndex (Q T a) ≤ (q)^4 := by
    rw [hqn,horder,Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,←pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  exact hsmall

/-- The four-conjugate source argument applies to the actual field-sized
subgroup of a plane radical, with its centralizer measured on the whole core. -/
theorem core_eq_moving_sup_fixed_of_plane_root
    (g : Geometry d.radical) (hb : g.b d.radical=2)
    {a t : Vertex d.radical} (ha : color d.radical a=false)
    (hat : Adjacent d.radical a t)
    (cv : RadicalPlaneCover d.radical (replacementMovedSection h d) n a t)
    (B : Subgroup (FreeAmalgam d.radical)) (hBT : B ≤ Q d.radical t)
    (hcard : (Q d.radical a).relIndex B=2^n)
    (hfixed : (centralizer (B : Set (FreeAmalgam d.radical))).relIndex (Z d.radical a)=2^n)
    (hindex : (centralizer (B : Set (FreeAmalgam d.radical))).relIndex (Q d.radical a) ≤ 2^n) :
    Q d.radical a=U d.radical a ⊔ fixedCore d.radical a := by
  let E := cv.field
  let e := cv.equiv
  let κ := cv.quotient
  let β := cv.actor
  let βB := β.comp (inclusion hBT)
  have hTS := cv.edge_le
  have hq : 1<2^n := one_lt_pow₀ (by decide : 1<(2:ℕ)) (by have := h.nonbinary; omega)
  let f := Classical.choose (plane_root_generating_conjugates h d g hb ha hat cv B hBT hcard hfixed)
  have hf := Classical.choose_spec (plane_root_generating_conjugates h d g hb ha hat cv B hBT hcard hfixed)
  let s := Classical.choose (replacement_wholeKernelQuotient_over h d g hb ha κ cv.onto cv.kernel_Q)
  have hs := Classical.choose_spec (replacement_wholeKernelQuotient_over h d g hb ha κ cv.onto cv.kernel_Q)
  let γ := (replacementComponent d).subtype.comp e.groupEquiv.symm.toMonoidHom
  let σ := s.action.comp γ
  have hBS : B ≤ stabilizer d.radical a := hBT.trans hTS
  have hmap : (B.subgroupOf (stabilizer d.radical a)).map κ=βB.range.map γ := by
    rw [←MonoidHom.range_comp]
    apply le_antisymm
    · rintro u ⟨b,hb,rfl⟩
      refine ⟨⟨b.val,hb⟩,?_⟩
      exact cv.actor_marking (inclusion hBT ⟨b.val,hb⟩)
    · rintro u ⟨b,rfl⟩
      exact ⟨inclusion hBS b,b.property,(cv.actor_marking (inclusion hBT b)).symm⟩
  have hSN : stabilizer d.radical a ≤ normalizer
      (fixedCore d.radical a : Set (FreeAmalgam d.radical)) := by
    have hSL : stabilizer d.radical a ≤ normalizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) := by
      have ht := le_normalizer_map (H := pResidual 2 (stabilizer d.radical a))
        (stabilizer d.radical a).subtype
      rw [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] at ht
      exact ht
    exact (le_inf (Q_normalized d.radical a)
      (hSL.trans (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf
  let := finite_stabilizer d.radical a
  let : Finite (Q d.radical a) := Finite.of_injective
    (inclusion (show Q d.radical a ≤ stabilizer d.radical a from fun _ hx => hx.1))
    (inclusion_injective _)
  have hfullfixed : fixedSpace σ ⊤=⊥ := by
    apply bot_unique
    intro v hv
    apply s.fixed_eq_bot.le
    rintro ⟨x,hx⟩
    rw [hs,cv.component] at hx
    obtain ⟨b,hb⟩ := e.groupEquiv.symm.surjective ⟨x,hx⟩
    have he : γ b=x := congrArg Subtype.val hb
    change s.action x v=v
    rw [←he]
    exact hv ⟨b,mem_top _⟩
  have hsmall := whole_core_index_bound_of_conjugates d.radical a s (2^n) n rfl
    B hBS hSN γ βB.range f hf (by rw [hs]; exact hmap) hfullfixed hindex
  rw [core_fixed_index_eq_natural_mul h d g hb ha] at hsmall
  have hrel : (U d.radical a ⊔ fixedCore d.radical a).relIndex (Q d.radical a)=1 := by
    have hp : 0<(2^n)^4 := pow_pos (by omega) _
    have hlo : 0<(U d.radical a ⊔ fixedCore d.radical a).relIndex (Q d.radical a) :=
      Nat.pos_of_ne_zero index_ne_zero_of_finite
    nlinarith only [hp,hlo,hsmall]
  apply le_antisymm (relIndex_eq_one.mp hrel)
  exact sup_le ((U_le_Z a).trans
    ((g.omega_bound a ha (by rw [g.distance_constant a ha]; change 0<g.b d.radical; omega)).trans
      (omegaCenter_le _))) inf_le_left

private theorem fixedCore_le_opposite_of_large_pair
    (g : Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hcritical : (2^n)^2 ≤ (Q d.radical z).relIndex (Z d.radical a)) :
    fixedCore d.radical a ≤ Q d.radical z := by
  obtain ⟨_,_,_,_,hRa,hRz,_⟩ :=
    source_four_large_paired_geometry h d g hb hsat path hat hzt c c' hcritical
  have hA := source_four_fixed_attachments h d g hb hsat path hat hzt c c'
  let D := fixedCore d.radical a
  have hDQ : D ≤ Q d.radical a := inf_le_left
  have hZT : Z d.radical z ≤ Q d.radical t :=
    ((g.omega_bound z path.end_color (by
      rw [g.distance_constant z path.end_color]; change 0<g.b d.radical; omega)).trans
      (omegaCenter_le _)).trans c'.core_le_edge
  have hmove : ⁅D,U d.radical z⁆ ≤
      U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical)) := by
    rw [←hA]
    apply le_inf
    · apply (commutator_mono (hDQ.trans c.core_le_edge) (U_le_Z z)).trans
      rw [commutator_comm,hRz,←hRa]
      exact full_radical_Z_displacement_le_moving h d g (by omega) path.start_color c
    · apply le_trans ?_ (show D ≤ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) from inf_le_right)
      exact le_normalizer_iff_commutator_le_left.mp
        (((U_le_Z z).trans hZT).trans c.fixedCore_normalized)
  have hc : D ≤ centralizer (U d.radical z : Set (FreeAmalgam d.radical)) := by
    intro b hbD u hu
    exact (commutatorElement_eq_one_iff_commute.mp
      (stabilizer_value_in_fixed_eq_one h d g (by omega) path.end_color c' b
        (c'.edge_le (c.core_le_edge (hDQ hbD))) u hu
        (hmove (commutator_mem_commutator hbD hu)).2)).eq.symm
  rw [←stabilizer_centralizer_moving_eq_core h d path.end_color]
  exact le_inf ((hDQ.trans c.core_le_edge).trans c'.edge_le) hc

omit h [Finite H] in
private theorem core_decomposition_at
    {a b : Vertex d.radical} (ha : color d.radical a=false) (hb : color d.radical b=false)
    (hcore : Q d.radical a=U d.radical a ⊔ fixedCore d.radical a) :
    Q d.radical b=U d.radical b ⊔ fixedCore d.radical b := by
  obtain ⟨x,hx⟩ := exists_mVertex_of_color d.radical ha
  obtain ⟨y,hy⟩ := exists_mVertex_of_color d.radical hb
  have hab : act d.radical (x⁻¹*y) a=b := by
    rw [hx,hy,act_mVertex,mul_inv_cancel_left]
  have hD (k : FreeAmalgam d.radical) : fixedCore d.radical (act d.radical k a)=
      (fixedCore d.radical a).map (MulAut.conj k⁻¹).toMonoidHom := by
    have hc : (centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical))).map
        (MulAut.conj k⁻¹).toMonoidHom =
        centralizer ((Ltilde d.radical a).map (MulAut.conj k⁻¹).toMonoidHom : Set (FreeAmalgam d.radical)) := by
      apply le_antisymm
      · exact map_centralizer_le_centralizer_image _ _
      · intro z hz
        let e := MulAut.conj k⁻¹
        refine ⟨e.symm z,?_,e.apply_symm_apply z⟩
        intro w hw
        apply e.injective
        simpa only [map_mul,e.apply_symm_apply] using hz (e w) (mem_map_of_mem _ hw)
    rw [fixedCore,Q_act,Ltilde_act,fixedCore,map_inf _ _ _ (MulAut.conj k⁻¹).injective,hc]
  rw [←hab,Q_act,U_act,hD,←Subgroup.map_sup,←hcore]

/-- The commuting-coset contradiction at the end of source (6), with the
regular element and the full component-fixed core retained. -/
private theorem large_regular_conjugate_mem_core
    (g : Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hcritical : (2^n)^2 ≤ (Q d.radical z).relIndex (Z d.radical a))
    (hcore : Q d.radical a=U d.radical a ⊔ fixedCore d.radical a)
    (x w : FreeAmalgam d.radical) (hx : x ∈ Z d.radical z)
    (hreg : Z d.radical a ⊓ centralizer ({x} : Set (FreeAmalgam d.radical))=Z d.radical t)
    (hcoset : x⁻¹*w ∈ Q d.radical a) (hcomm : Commute x w) : w ∈ Q d.radical z := by
  have hD := fixedCore_le_opposite_of_large_pair h d g hb hsat path hat hzt c c' hcritical
  have hUD : U d.radical a ≤ centralizer (fixedCore d.radical a : Set (FreeAmalgam d.radical)) :=
    ((U_le_Z a).trans (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical a path.start_color))).trans (centralizer_le inf_le_left)
  rw [hcore,←SetLike.mem_coe,coe_mul_of_left_le_normalizer_right _ _
    (hUD.trans (Subgroup.centralizer_le_normalizer _))] at hcoset
  obtain ⟨u,hu,v,hv,he⟩ := hcoset
  change u*v=x⁻¹*w at he
  have hvx : Commute v x := (commutator_eq_bot_iff_le_centralizer.mp
    (Z_centralizes_Q d.radical z path.end_color)) hx v (hD hv)
  have hux : Commute u x := by
    have hprod : Commute (u*v) x := by
      rw [he]
      exact (Commute.refl x).inv_left.mul_left hcomm.symm
    change u*x=x*u
    apply mul_right_cancel (b := v)
    calc
      u*x*v=u*(v*x) := by rw [mul_assoc,hvx.eq]
      _ = (u*v)*x := (mul_assoc _ _ _).symm
      _ = x*(u*v) := hprod.eq
      _ = x*u*v := (mul_assoc _ _ _).symm
  have hut : u ∈ Z d.radical t := hreg ▸
    (show u ∈ Z d.radical a ⊓ centralizer ({x} : Set (FreeAmalgam d.radical)) from
      ⟨U_le_Z a hu,mem_centralizer_singleton_iff.mpr hux.eq⟩)
  have hZQ : Z d.radical z ≤ Q d.radical z :=
    (g.omega_bound z path.end_color (by
      rw [g.distance_constant z path.end_color]; change 0<g.b d.radical; omega)).trans (omegaCenter_le _)
  have hq : x⁻¹*w ∈ Q d.radical z := he ▸ (Q d.radical z).mul_mem
    (hZQ (Sp4Four.edge_Z_le_endpoint d.radical path.end_color hzt hut)) (hD hv)
  have hh := (Q d.radical z).mul_mem (hZQ hx) hq
  simpa only [mul_inv_cancel_left] using hh

/-- MS93 (3.7)(6): a genuine critical pair with image of field order exists.
The saturation premise concerns the original characteristic replacement. -/
theorem source_six_exists_field_critical_pair
    (g : Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical) :
    ∃ a z : Vertex d.radical, Nonempty (CriticalPath d.radical g a z) ∧
      (Q d.radical z).relIndex (Z d.radical a)=2^n := by
  let a := mVertex d.radical 1
  obtain ⟨z,⟨path⟩⟩ := CriticalPath.exists_from (R := d.radical) (geometry := g)
    (a := a) (show color d.radical a=false from rfl)
  by_cases hcritical : (2^n)^2 ≤ (Q d.radical z).relIndex (Z d.radical a)
  swap
  · exact ⟨a,z,⟨path⟩,(replacement_critical_indices_eq_field_of_small h d path (by omega)
      (lt_of_not_ge hcritical)).1⟩
  have hd : (cosetGraph d.radical).dist a z=2 :=
    path.critical.1.trans ((g.distance_constant a path.start_color).trans hb)
  obtain ⟨t,hat,hzt⟩ := exists_common_neighbor_of_dist_two d.radical a z hd
  obtain ⟨c⟩ := exists_edgeMarking h d g (by omega) path.start_color hat
  obtain ⟨c'⟩ := exists_edgeMarking h d g (by omega) path.end_color hzt
  obtain ⟨x,hx,hxQ,hreg,y,hy,k,hk,he,hcoset,hcomm,hmove,⟨p⟩,halt⟩ :=
    source_six_field_pair_or_whole_core_centralizer h d g hb hsat path hat hzt c c' hcritical
  rcases halt with hsmall | ⟨hwQ,hi,hQi,hCi,hMi,hne,hwhole⟩
  · exact ⟨act d.radical k⁻¹ z,z,⟨p⟩,hsmall⟩
  let v := act d.radical k⁻¹ z
  by_cases hc : (2^n)^2 ≤ (Q d.radical z).relIndex (Z d.radical v)
  swap
  · exact ⟨v,z,⟨p⟩,(replacement_critical_indices_eq_field_of_small h d p (by omega)
      (lt_of_not_ge hc)).1⟩
  have hkt : act d.radical k⁻¹ t=t := (stabilizer d.radical t).inv_mem hk
  have hvt : Adjacent d.radical v t := by
    simpa only [hkt] using (adjacent_act_iff d.radical k⁻¹ z t).mpr hzt
  obtain ⟨cv⟩ := exists_edgeMarking h d g (by omega) p.start_color hvt
  obtain ⟨⟨pv⟩,_⟩ := source_four_large_paired_geometry h d g hb hsat p hvt hzt cv c' hc
  let X := Z d.radical z ⊓ centralizer ({y*x*y⁻¹} : Set (FreeAmalgam d.radical))
  have hZT : Z d.radical z ≤ Q d.radical t :=
    ((g.omega_bound z path.end_color (by
      rw [g.distance_constant z path.end_color]
      change 0<g.b d.radical
      omega)).trans (omegaCenter_le _)).trans c'.core_le_edge
  have hXT : X ≤ Q d.radical t := inf_le_left.trans hZT
  have hvcore := core_eq_moving_sup_fixed_of_plane_root h d g hb p.start_color hvt pv X hXT
    hQi hCi hwhole.le
  have hacore := core_decomposition_at d p.start_color path.start_color hvcore
  exact (hwQ (large_regular_conjugate_mem_core h d g hb hsat path hat hzt c c' hcritical
    hacore x (y*x*y⁻¹) hx hreg hcoset hcomm)).elim

/-- The immediate whole-core consequence of source (6) and source (3),
for every vertex of the original component color. This supplies the whole-core
premise of the subsequent source endgame without assuming a critical image. -/
theorem source_six_core_decomposition
    (g : Geometry d.radical) (hb : g.b d.radical=2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical)
    {a : Vertex d.radical} (ha : color d.radical a=false) :
    Q d.radical a=U d.radical a ⊔ fixedCore d.radical a := by
  obtain ⟨b,z,⟨path⟩,hcritical⟩ := source_six_exists_field_critical_pair h d g hb hsat
  have hd : (cosetGraph d.radical).dist b z=2 :=
    path.critical.1.trans ((g.distance_constant b path.start_color).trans hb)
  obtain ⟨t,hbt,hzt⟩ := exists_common_neighbor_of_dist_two d.radical b z hd
  obtain ⟨c⟩ := exists_edgeMarking h d g (by omega) path.start_color hbt
  obtain ⟨c'⟩ := exists_edgeMarking h d g (by omega) path.end_color hzt
  have hcore := (source_three_of_field_critical h d g hb hsat path hbt hzt c c' hcritical).2.1
  exact core_decomposition_at d path.start_color ha hcore

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
