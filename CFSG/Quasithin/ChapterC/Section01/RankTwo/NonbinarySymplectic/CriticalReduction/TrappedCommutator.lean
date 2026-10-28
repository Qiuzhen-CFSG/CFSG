module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.TrappedTransport

/-!
# The whole moving-layer commutator after the terminal twist

A field-sized fixed index on a full symplectic cover gives a natural fixed
hyperplane. Any field-subspace preimage moved by the actor supplements that
hyperplane, including the entire covering kernel. Its commutator therefore
equals the commutator on the whole cover. No central complement is chosen.

Applied to the actual terminal residual twist, this identifies the same
order-q source commutator with the whole-U commutator at the twisted endpoint
and, after inverse conjugation, at the original endpoint. The original path,
selected neighbor, all fixed indices and literal conjugation maps are retained.
TrappedRootComparison supplies the remaining original-root containment.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two,
MS93 (5.8), printed p.920.
-/

public noncomputable section
open Subgroup Representation Representation.OneCohomology
open Theory.SpecificGroups.SymplecticFour Theory.GroupTheory
open Representation.SymplecticFourOrthogonalCover
open scoped commutatorElement IsMulCommutative

private theorem fixed_preimage_iff
    {F W G : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W] [Group G]
    {σ : Representation (ZMod 2) (L (K := F)) W}
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (j : Multiplicative W →* G) (hj : Function.Injective j)
    (Y : Subgroup G) (β : Y →* L (K := F))
    (hact : ∀ (y : Y) (w : W), j (Multiplicative.ofAdd (σ (β y) w)) =
      y.val*j (Multiplicative.ofAdd w)*y.val⁻¹) (w : W) :
    j (Multiplicative.ofAdd w) ∈ centralizer (Y : Set G) ↔
      p w ∈ TwoLocalCover.fixedSpace ((commutator (Sp F)).subtype.comp β).range := by
  constructor
  · intro hw y hy
    obtain ⟨y,rfl⟩ := hy
    have he : σ (β y) w=w := by
      apply Multiplicative.ofAdd.injective
      apply hj
      rw [hact,hw y.val y.property,mul_inv_cancel_right]
    exact (LinearMap.congr_fun (p.isIntertwining' (β y)) w).symm.trans (congrArg p he)
  · intro hw y hy
    have hf := cover_fixed_of_projection_fixed p hp (β ⟨y,hy⟩) w
      (hw _ ⟨⟨y,hy⟩,rfl⟩)
    have he := congrArg (fun w => j (Multiplicative.ofAdd w)) hf
    rw [hact,mul_inv_eq_iff_eq_mul] at he
    exact he

private theorem embedded_fixed_hyperplane_commutator
    {F W G : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W] [Group G]
    {σ : Representation (ZMod 2) (L (K := F)) W}
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (j : Multiplicative W →* G) (hj : Function.Injective j)
    (Y T : Subgroup G) (β : Y →* L (K := F)) (γ : T →* L (K := F))
    (hact : ∀ (y : Y) (w : W), j (Multiplicative.ofAdd (σ (β y) w)) =
      y.val*j (Multiplicative.ofAdd w)*y.val⁻¹)
    (hactT : ∀ (t : T) (w : W), j (Multiplicative.ofAdd (σ (γ t) w)) =
      t.val*j (Multiplicative.ofAdd w)*t.val⁻¹)
    (hi : (centralizer (Y : Set G)).relIndex j.range = Nat.card F)
    (hn : ⁅Y,j.range ⊓ centralizer (T : Set G)⁆ ≠ ⊥) :
    ⁅Y,j.range ⊓ centralizer (T : Set G)⁆ = ⁅Y,j.range⁆ := by
  let α := (commutator (Sp F)).subtype.comp β
  let τ := (commutator (Sp F)).subtype.comp γ
  let N := TwoLocalCover.fixedSpace α.range
  let A := TwoLocalCover.fixedSpace τ.range
  have hfixed : BinaryOffender.fixedSpace (binaryNatural (K := F)) β.range =
      N.restrictScalars (ZMod 2) := by
    ext v
    constructor
    · intro hv x hx
      obtain ⟨y,rfl⟩ := hx
      exact hv ⟨β y,⟨y,rfl⟩⟩
    · intro hv x
      obtain ⟨y,hy⟩ := x.property
      change binaryNatural x.val v=v
      rw [←hy]
      exact hv (α y) ⟨y,rfl⟩
  have hidx := BinaryOffender.embedded_centralizer_index σ j.range Y j hj rfl β hact
  rw [fixedCodim_of_binaryCover p hp] at hidx
  have hc : Nat.card (Vector F ⧸ N) = Nat.card F := by
    rw [hi] at hidx
    change Nat.card F = 2 ^ Module.finrank (ZMod 2)
      (Vector F ⧸ BinaryOffender.fixedSpace (binaryNatural (K := F)) β.range) at hidx
    rw [hfixed] at hidx
    have he := Nat.card_congr (Submodule.Quotient.restrictScalarsEquiv (ZMod 2) N).toEquiv
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at he
    exact he.symm.trans hidx.symm
  have hd : Module.finrank F (Vector F ⧸ N)=1 := by
    rw [Module.natCard_eq_pow_finrank (K := F)] at hc
    exact (Nat.pow_right_injective (by exact Finite.one_lt_card : 1 < Nat.card F))
      (hc.trans (pow_one _).symm)
  have hdim : Module.finrank F N=3 := by
    have hh := N.finrank_quotient_add_finrank
    rw [hd] at hh
    have hv : Module.finrank F (Vector F)=4 := by simp [Theory.SpecificGroups.SymplecticFour.Vector]
    omega
  have hnot : ¬ A ≤ N := by
    intro hle
    apply hn
    apply commutator_eq_bot_iff_le_centralizer.mpr
    apply le_centralizer_iff.mp
    rintro u ⟨hu,ht⟩
    obtain ⟨w,rfl⟩ := hu
    exact (fixed_preimage_iff p hp j hj Y β hact w.toAdd).mpr
      (hle ((fixed_preimage_iff p hp j hj T γ hactT w.toAdd).mp ht))
  have htop : A ⊔ N = ⊤ := by
    have hle : N ≤ A ⊔ N := le_sup_right
    have hlow := Submodule.finrank_mono hle
    have hu := (A ⊔ N).finrank_le
    have hv : Module.finrank F (Vector F)=4 := by simp [Theory.SpecificGroups.SymplecticFour.Vector]
    have hneq : Module.finrank F (A ⊔ N : Submodule F (Vector F)) ≠ 3 := by
      intro he
      have hn' := Submodule.eq_of_le_of_finrank_eq hle (hdim.trans he.symm)
      exact hnot (le_sup_left.trans hn'.ge)
    apply Submodule.eq_top_of_finrank_eq
    omega
  apply le_antisymm (commutator_mono le_rfl inf_le_left)
  apply commutator_le.mpr
  intro y hy u hu
  obtain ⟨w,rfl⟩ := hu
  obtain ⟨a,ha,b,hb,hab⟩ := Submodule.mem_sup.mp (show p w.toAdd ∈ A ⊔ N from htop.symm ▸ Submodule.mem_top)
  obtain ⟨v,hv⟩ := hp.1 a
  let k := w.toAdd-v
  have hk : p k=b := by dsimp [k]; rw [map_sub,hv,←hab]; abel
  have hvT : j (Multiplicative.ofAdd v) ∈ centralizer (T : Set G) :=
    (fixed_preimage_iff p hp j hj T γ hactT v).mpr (hv ▸ ha)
  have hkY : j (Multiplicative.ofAdd k) ∈ centralizer (Y : Set G) :=
    (fixed_preimage_iff p hp j hj Y β hact k).mpr (hk ▸ hb)
  have hw : j w=j (Multiplicative.ofAdd v)*j (Multiplicative.ofAdd k) := by
    rw [←map_mul,←ofAdd_add]
    congr 1
    apply Multiplicative.toAdd.injective
    change w.toAdd = v + (w.toAdd-v)
    abel
  rw [hw,commutatorElement_mul_right_eq_mul_conj,
    commutatorElement_eq_one_iff_mul_comm.mpr (hkY y hy),mul_one,mul_inv_cancel_right]
  exact commutator_mem_commutator hy ⟨⟨_,rfl⟩,hvT⟩

open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- A nontrivial commutator on a full fixed subgroup equals the whole-U
commutator when the acting subgroup has fixed index q. -/
theorem Input.replacement_field_index_commutator_on_fixed_subgroup
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {z : Vertex d.radical} (hz : color d.radical z=false)
    (Y T : Subgroup (FreeAmalgam d.radical))
    (hYS : Y ≤ stabilizer d.radical z) (hTS : T ≤ stabilizer d.radical z)
    (hi : (centralizer (Y : Set (FreeAmalgam d.radical))).relIndex (U d.radical z)=Nat.card F)
    (hn : ⁅Y,U d.radical z ⊓ centralizer (T : Set (FreeAmalgam d.radical))⁆ ≠ ⊥) :
    ⁅Y,U d.radical z ⊓ centralizer (T : Set (FreeAmalgam d.radical))⁆ = ⁅Y,U d.radical z⁆ := by
  let q := QuotientGroup.mk' (pCore 2 d.overgroup)
  let C := (K.subgroupOf d.overgroup).map q
  let : C.Normal := (h.replacement_component_image_structure d).2.1
  let : IsElementaryAbelian 2 (omegaCenterIn (pCore 2 d.overgroup)) := omegaCenterIn_elementary _
  let s := MovedSection.ofNormal (NormalElementaryQuotient.representation
    (omegaCenterIn (pCore 2 d.overgroup)) q (QuotientGroup.mk'_surjective _)
    ((QuotientGroup.ker_mk' _).trans (h.replacement_centralOmega_centralizer d).symm)) C
  obtain ⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hψ,hsemi,hconj,hproj,hker⟩ :=
    h.replacement_ambient_initial_cover_at_vertex d hz
  have hFc : Nat.card E.Carrier=Nat.card F := by rw [E.card_eq,hE,h.field_card]
  have hCtop : C=⊤ := by
    have hh : C.comap q=⊤ := by
      rw [show C=(K.subgroupOf d.overgroup).map q from rfl,comap_map_eq,QuotientGroup.ker_mk']
      exact h.replacement_inner_of_four_le d geometry hb
    rw [←map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) C,hh,
      ←MonoidHom.range_eq_map,MonoidHom.range_eq_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  let κC := κ.codRestrict C (fun x => hCtop ▸ mem_top (κ x))
  let γ := e.groupEquiv.toMonoidHom.comp κC
  let σ := MovedSection.coverAction s e
  have hact (y : stabilizer d.radical z) (w : s.space.toSubmodule) :
      j (Multiplicative.ofAdd (σ (γ y) w))=y.val*j (Multiplicative.ofAdd w)*y.val⁻¹ := by
    change j (Multiplicative.ofAdd (s.space.toRepresentation
      (e.groupEquiv.symm (e.groupEquiv (κC y))) w))=_
    rw [e.groupEquiv.symm_apply_apply]
    exact hconj y w
  have hh := embedded_fixed_hyperplane_commutator (MovedSection.coverProjection s e) he j hj
    Y T (γ.comp (inclusion hYS)) (γ.comp (inclusion hTS))
    (fun y w => hact (inclusion hYS y) w) (fun t w => hact (inclusion hTS t) w)
    (by rwa [hjr,hFc]) (by rwa [hjr])
  rwa [hjr] at hh


/-- The same terminal twist and selected neighbor give both whole-U
commutator equalities, preserving the original full trapped configuration. -/
theorem Input.replacement_trapped_radius_whole_commutator_configuration
    {geometry : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t) (hfirst : path.walk.getVert 1=t)
    (htrap : V d.radical a ≤ Q d.radical (path.walk.getVert (path.walk.length-2))) :
    let p := path.walk.getVert (path.walk.length-2)
    let A := U d.radical z ⊓ Q d.radical a
    A = U d.radical z ⊓ B d.radical p (geometry.Z_normal p) ∧
    (Q d.radical a).relIndex (U d.radical z)=Nat.card F ∧
    (∀ v w c : Vertex d.radical, color d.radical v=false →
      Adjacent d.radical v w → Adjacent d.radical c w →
      (B d.radical v (geometry.Z_normal v)).relIndex (U d.radical c) ≤ Nat.card F) ∧
    ∃ x u y, x ∈ Ltilde d.radical p ∧
      act d.radical x (path.walk.getVert (path.walk.length-1))=
        path.walk.getVert (path.walk.length-3) ∧
      (B d.radical p (geometry.Z_normal p)).relIndex (U d.radical (act d.radical x z))=
        Nat.card F ∧
      Adjacent d.radical u t ∧ y ∈ stabilizer d.radical a ∧
      let v := act d.radical y u
      let w := act d.radical y t
      let A' := U d.radical (act d.radical x z) ⊓ B d.radical p (geometry.Z_normal p)
      let D := ⁅Z d.radical v,A⁆
      Adjacent d.radical a w ∧ Adjacent d.radical v w ∧
      Z d.radical v ≤ Q d.radical p ∧
      ¬ Z d.radical z ≤ normalizer
        ((Z d.radical v ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) ∧
      (Q d.radical z).relIndex (Z d.radical a)=Nat.card F ∧
      (Q d.radical a).relIndex (Z d.radical z)=Nat.card F ∧
      (centralizer (A : Set (FreeAmalgam d.radical))).relIndex (U d.radical v)=Nat.card F ∧
      (centralizer (A : Set (FreeAmalgam d.radical))).relIndex (Z d.radical v)=Nat.card F ∧
      A.map (MulAut.conj x⁻¹).toMonoidHom=A' ∧
      A ⊔ Z d.radical p=A' ⊔ Z d.radical p ∧
      D ≤ centralizer (Ltilde d.radical p : Set (FreeAmalgam d.radical)) ∧
      D.map (MulAut.conj x⁻¹).toMonoidHom=D ∧
      D=⁅Z d.radical v,A'⁆ ∧
      D=⁅Z d.radical (act d.radical x⁻¹ v),A⁆ ∧
      D=⁅Z d.radical v,U d.radical (act d.radical x z)⁆ ∧
      D=⁅Z d.radical (act d.radical x⁻¹ v),U d.radical z⁆ ∧
      Nat.card D=Nat.card F ∧
      ¬ D ≤ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical)) ∧
      ∃ hv : color d.radical v=false,
        CriticalPair d.radical v (act d.radical x z) (geometry.exists_critical v hv) ∧
        (Q d.radical v).relIndex (U d.radical (act d.radical x z))=Nat.card F ∧
        (centralizer (Z d.radical v : Set (FreeAmalgam d.radical))).relIndex
          (U d.radical (act d.radical x z))=Nat.card F := by
  obtain ⟨hA,hAQ,hbound,x,u,y,hx,htwist,hiB,hut,hy,haw,hvw,htrapv,hn,
      hi,hi',hU,hZ,hmap,hjoin,hfixed,hinv,hcomm,hback,hcard,hnot,hv,hcritical,hnewQ,hnewC⟩ :=
    h.replacement_trapped_radius_transported_configuration d path hb hat hfirst htrap
  let v := act d.radical y u
  let A := U d.radical z ⊓ Q d.radical a
  let D := ⁅Z d.radical v,A⁆
  let z' := act d.radical x z
  let A' := U d.radical z' ⊓ B d.radical (path.walk.getVert (path.walk.length-2)) (geometry.Z_normal _)
  have hYS : Z d.radical v ≤ stabilizer d.radical z' :=
    Z_le_stabilizer_of_dist_le v (geometry.exists_critical v hv) hcritical.1.le
  have hTS : Z d.radical (act d.radical x a) ≤ stabilizer d.radical z' :=
    Z_le_stabilizer_of_dist_le _ (geometry.exists_critical _ (path.act x).start_color)
      (path.act x).critical.1.le
  have hCa := MSCentralOrbit.C_eq_Q d.radical (h.replacement_two_group d)
    (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d) a path.start_color
  have hUS : U d.radical z ≤ stabilizer d.radical a :=
    (U_le_Z z).trans (path.endpoint_Z_le_start_stabilizer (by omega))
  have hfix : A = U d.radical z ⊓ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) := by
    dsimp only [A]
    rw [←hCa]
    ext r
    exact ⟨fun hr => ⟨hr.1,hr.2.2⟩,fun hr => ⟨hr.1,hUS hr.1,hr.2⟩⟩
  have hfix' : A' = U d.radical z' ⊓
      centralizer (Z d.radical (act d.radical x a) : Set (FreeAmalgam d.radical)) := by
    change A.map (MulAut.conj x⁻¹).toMonoidHom=A' at hmap
    rw [←hmap,hfix,←map_inf_centralizer_of_injective _ (MulAut.conj x⁻¹).injective,
      ←U_act,←Z_act]
  have hne : ⁅Z d.radical v,A'⁆ ≠ ⊥ := by
    intro he
    exact hnot (hcomm ▸ he ▸ bot_le)
  have hwhole : D=⁅Z d.radical v,U d.radical z'⁆ := by
    change D=⁅Z d.radical v,A'⁆ at hcomm
    refine hcomm.trans ?_
    rw [hfix'] at hne ⊢
    exact h.replacement_field_index_commutator_on_fixed_subgroup d geometry hb
      (by rw [action_preserves_color]; exact path.end_color)
      (Z d.radical v) (Z d.radical (act d.radical x a)) hYS hTS hnewC hne
  have hDmap : D.map (MulAut.conj x).toMonoidHom=D :=
    mem_normalizer_iff_map_conj_eq.mp ((Subgroup.centralizer_le_normalizer _)
      ((le_centralizer_iff.mp hfixed) hx))
  have hwholeBack : D=⁅Z d.radical (act d.radical x⁻¹ v),U d.radical z⁆ := by
    have hh := congrArg (Subgroup.map (MulAut.conj x).toMonoidHom) hwhole
    rw [hDmap,map_commutator] at hh
    have hZmap : (Z d.radical v).map (MulAut.conj x).toMonoidHom =
        Z d.radical (act d.radical x⁻¹ v) := by rw [Z_act d.radical x⁻¹ v,inv_inv]
    have hid : (MulAut.conj x).toMonoidHom.comp (MulAut.conj x⁻¹).toMonoidHom = MonoidHom.id _ := by
      apply MonoidHom.ext
      intro r
      simp [MulAut.conj_apply,mul_assoc]
    change D=⁅(Z d.radical v).map (MulAut.conj x).toMonoidHom,
      (U d.radical (act d.radical x z)).map (MulAut.conj x).toMonoidHom⁆ at hh
    rw [hZmap,U_act,map_map,hid,Subgroup.map_id] at hh
    exact hh
  exact ⟨hA,hAQ,hbound,x,u,y,hx,htwist,hiB,hut,hy,haw,hvw,htrapv,hn,
    hi,hi',hU,hZ,hmap,hjoin,hfixed,hinv,hcomm,hback,hwhole,hwholeBack,hcard,hnot,
    hv,hcritical,hnewQ,hnewC⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
