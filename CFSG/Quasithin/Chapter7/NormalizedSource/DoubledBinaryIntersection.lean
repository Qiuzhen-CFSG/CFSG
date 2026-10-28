module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinarySylow
public import CFSG.Quasithin.Chapter1.Section01Inheritance
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.GeneralizedFitting.RelativeComponent
public import Theory.GroupTheory.GeneralizedFitting.SylowNormalizedComponent
-- Internal companion for the paired-plane coordinate calculation.
import all CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPlanes
/-!
# Characteristic two in the actual binary point-centralizer intersections

A Sylow subgroup of C_G(U,w) containing Q lies in M by Thompson
normalizer control. Its conjugation into the original local base can be
performed by an element centralizing the whole orbit: the paired-plane
fixer is already induced by the original component. Normality therefore
puts O₂(C_G(U,w)) in the base. Source 1.1.4(4) then gives characteristic
two for H ∩ C_G(w), with the relative two-cores kept in their actual groups.

The residual moving subgroup is complementary to U and has order sixteen.
The odd-rank component-orbit bound makes this subgroup normalize each ordinary
component. Its literal induced automizer therefore has order sixteen as soon
as the component fixed-space calculation excludes a centralizer kernel.

The chosen-module application in NonFFSourceDoubledBinaryIntersection
discharges the Sylow, factorization and ambient characteristic-two inputs.
Source: Aschbacher–Smith 7.7.5, printed p.704, refs/quasithin.pdf.
The printed display names F*(C_G(w)); its proof and the application in
7.7.6 establish F*(C_H(w)) = O₂(C_H(w)), which is the conclusion used here.
-/

open Subgroup Stellmacher
open scoped Pointwise IsMulCommutative commutatorElement
public noncomputable section
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryIntersection

/-- The source Sylow-conjugacy argument, with the conjugating kernel fixed pointwise. -/
theorem doubleCentralizer_core_le_base
    {G : Type*} [Group G] [Finite G]
    (W U B M Q : Subgroup G) (T : Sylow 2 G)
    (hUW : U ≤ W) (hTM : (T : Subgroup G) ≤ M)
    (hpQ : IsPGroup 2 Q) (hQC : Q ≤ centralizer (W : Set G))
    (hJQ : elementaryAbelianMaxJ (T : Subgroup G) ≤ Q)
    (hcontrol : ∀ R : Subgroup G, IsPGroup 2 R →
      elementaryAbelianMaxJ (T : Subgroup G) ≤ R → R ≤ M)
    (S₀ : Sylow 2 (centralizer (U : Set G)))
    (hS₀ : (S₀ : Subgroup _).map (centralizer (U : Set G)).subtype =
      (T : Subgroup G) ⊓ centralizer (U : Set G))
    (hTB : (T : Subgroup G) ⊓ centralizer (U : Set G) ≤ B)
    (hfactor : ∀ m ∈ M ⊓ centralizer (U : Set G),
      ∃ b ∈ B, ∃ c ∈ centralizer (W : Set G), m = b * c)
    (w : G) (hw : w ∈ W) :
    (centralizer (U : Set G) ⊓ centralizer ({w} : Set G)).pCoreIn 2 ≤ B := by
  let X := centralizer (U : Set G) ⊓ centralizer ({w} : Set G)
  let M₀ := M ⊓ centralizer (U : Set G)
  have hCX : centralizer (W : Set G) ≤ X :=
    le_inf (centralizer_le hUW) (centralizer_le (Set.singleton_subset_iff.mpr hw))
  have hQX : Q ≤ X := hQC.trans hCX
  obtain ⟨S,hQS⟩ := (hpQ.comap_subtype (K := X)).exists_le_sylow
  let R := (S : Subgroup X).map X.subtype
  have hQR : Q ≤ R := by
    intro x hx
    exact mem_map_of_mem X.subtype (hQS (show (⟨x,hQX hx⟩ : X) ∈ Q.subgroupOf X from hx))
  have hRM : R ≤ M := hcontrol R (S.isPGroup'.map X.subtype) (hJQ.trans hQR)
  have hRM₀ : R ≤ M₀ := le_inf hRM ((map_subtype_le _).trans inf_le_left)
  obtain ⟨S₁,hS₁⟩ := DoubledBinarySylow.sylow_between
    (show M₀ ≤ centralizer (U : Set G) from inf_le_right) S₀
    (hS₀.trans_le (le_inf (inf_le_left.trans hTM) inf_le_right))
  obtain ⟨A,hRA⟩ := ((S.isPGroup'.map X.subtype).comap_subtype (K := M₀)).exists_le_sylow
  obtain ⟨m,hm⟩ := MulAction.exists_smul_eq M₀ A S₁
  obtain ⟨b,hb,c,hc,hbc⟩ := hfactor m m.property
  have hmap : R.map (MulAut.conj (m : G)).toMonoidHom ≤ B := by
    rintro _ ⟨x,hx,rfl⟩
    have hh : (MulAut.conj m) (⟨x,hRM₀ hx⟩ : M₀) ∈ (S₁ : Subgroup M₀) := by
      rw [← hm]
      exact mem_map_of_mem (MulAut.conj m).toMonoidHom (hRA hx)
    have hh' := mem_map_of_mem M₀.subtype hh
    rw [hS₁,hS₀] at hh'
    exact hTB hh'
  have hn : X ≤ normalizer (X.pCoreIn 2 : Set G) :=
    X.le_normalizer.trans (normalizer_le_normalizer_characteristic_image X (pCore 2 X))
  intro x hx
  have hx' : c⁻¹ * x * c ∈ X.pCoreIn 2 := by
    simpa only [inv_inv] using (mem_normalizer_iff.mp (hn (X.inv_mem (hCX hc))) x).mp hx
  have hr : c⁻¹ * x * c ∈ R := pCoreIn_le_sylow X S hx'
  have hh := hmap (mem_map_of_mem (MulAut.conj (m : G)).toMonoidHom hr)
  change (m : G) * (c⁻¹ * x * c) * (m : G)⁻¹ ∈ B at hh
  rw [hbc] at hh
  have he : b*c * (c⁻¹*x*c) * (b*c)⁻¹ = b*x*b⁻¹ := by group
  rw [he] at hh
  exact (mem_normalizer_iff.mp (B.le_normalizer hb) x).mpr hh

open ChapterE Representation Representation.BinaryOffender BinaryLinearThree
open DoubledBinaryPlanes DoubledBinaryLocalCore

/-- Every actor fixing the paired plane is a component actor times an element
centralizing the whole original orbit. -/
theorem pairedPlane_factor
    {G : Type*} [_root_.Group G] (W₀ L B M : Subgroup G) [IsElementaryAbelian 2 W₀]
    (hLN : L ≤ normalizer (W₀ : Set G)) (hMN : M ≤ normalizer (W₀ : Set G))
    (q : L →* BinaryLinearThree.Group) (hq : Function.Surjective q)
    (E : Additive W₀ ≃ₗ[ZMod 2] NaturalDual.Space)
    (a : Automizer W₀ ≃* MulAut BinaryLinearThree.Group)
    (ha : ∀ l, a (W₀.normalizerMonoidHom.rangeRestrict (inclusion hLN l)) = MulAut.conj (q l))
    (hcov : ∀ b g w, E (automizerRepresentation W₀ b (E.symm (NaturalDual.action g (E w)))) =
      NaturalDual.action (a b g) (E (automizerRepresentation W₀ b w)))
    (v : Vector) (f : Module.Dual (ZMod 2) Vector) (hfv : f v = 1)
    (hLB : L ⊓ centralizer (ambientPlane W₀ E v f : Set G) ≤ B) :
    ∀ m ∈ M ⊓ centralizer (ambientPlane W₀ E v f : Set G),
      ∃ b ∈ B, ∃ c ∈ centralizer (W₀ : Set G), m = b * c := by
  intro m hm
  let n : normalizer (W₀ : Set G) := ⟨m,hMN hm.1⟩
  have hi : W₀.normalizerMonoidHom.rangeRestrict n ∈
      inducedAutomizer W₀ (centralizer (ambientPlane W₀ E v f : Set G)) := ⟨n,hm.2,rfl⟩
  rw [← component_centralizer_image W₀ L hLN q hq E a ha hcov v f hfv] at hi
  obtain ⟨l,hl,he⟩ := hi
  let c := l⁻¹ * n
  have hc : (c : G) ∈ centralizer (W₀ : Set G) := by
    have hh : W₀.normalizerMonoidHom c = 1 := by
      change W₀.normalizerMonoidHom (l⁻¹ * n) = 1
      have he' : W₀.normalizerMonoidHom l = W₀.normalizerMonoidHom n :=
        congrArg Subtype.val he
      rw [map_mul,map_inv,he',inv_mul_cancel]
    change c ∈ W₀.normalizerMonoidHom.ker at hh
    rw [normalizerMonoidHom_ker] at hh
    exact hh
  exact ⟨l,hLB hl,c,hc,by change m = (l : G) * ((l : G)⁻¹ * m); group⟩

/-- The core-centralizer hypothesis of source 1.1.4(4) follows from the
actual two-core of the double centralizer. -/
theorem intersection_characteristicTwo
    {G : Type*} [_root_.Group G] [Finite G]
    (U H : Subgroup G) (w : G) (hp : IsPGroup 2 U)
    (hUH : U ≤ H) (hHC : H ≤ centralizer (U : Set G))
    (hUw : U ≤ centralizer ({w} : Set G))
    (hw : centralizer ({w} : Set G) ∈ Chapter1.He G)
    (hcore : (centralizer (U : Set G) ⊓ centralizer ({w} : Set G)).pCoreIn 2 ≤ H) :
    H ⊓ centralizer ({w} : Set G) ∈ Chapter1.He G := by
  let C := centralizer ({w} : Set G)
  let X := centralizer (U : Set G) ⊓ C
  let N := H ⊓ C
  have hUN : U ≤ N.pCoreIn 2 := le_pCoreIn_of_normalizes hp (le_inf hUH hUw)
    ((inf_le_left.trans hHC).trans (Subgroup.centralizer_le_normalizer _))
  have hP : C.pCoreIn 2 ⊓ centralizer (U : Set G) ≤ X.pCoreIn 2 := by
    apply le_pCoreIn_of_normalizes ((isPGroup_pCoreIn 2 C).to_le inf_le_left)
      (le_inf inf_le_right (inf_le_left.trans (pCoreIn_le 2 C)))
    apply le_trans _ inf_normalizer_le_normalizer_inf
    exact le_inf
      (inf_le_right.trans (C.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image C (pCore 2 C))))
      (inf_le_left.trans (centralizer (U : Set G)).le_normalizer)
  apply pCoreIn_selfCentralizing_of_core_centralizer_le hw (show N ≤ C from inf_le_right)
  intro x hx
  exact ⟨hcore (hP ⟨hx.1,centralizer_le hUN hx.2⟩),pCoreIn_le 2 C hx.1⟩

/-- The moving subgroup of the original local residual is disjoint from
the paired plane, in the original ambient group. -/
theorem pairedPlane_residual_disjoint
    {G : Type*} [_root_.Group G] (W₀ L : Subgroup G) [IsElementaryAbelian 2 W₀]
    (hLN : L ≤ normalizer (W₀ : Set G)) (q : L →* BinaryLinearThree.Group)
    (E : Additive W₀ ≃ₗ[ZMod 2] NaturalDual.Space)
    (hE : ∀ l w, E (automizerRepresentation W₀
      (W₀.normalizerMonoidHom.rangeRestrict (inclusion hLN l)) w) =
        NaturalDual.action (q l) (E w))
    (v : Vector) (f : Module.Dual (ZMod 2) Vector) (hfv : f v = 1) :
    Disjoint (ambientPlane W₀ E v f) ⁅W₀,localResidual L (ambientPlane W₀ E v f)⁆ := by
  let U := ambientPlane W₀ E v f
  let R := localResidual L U
  let π : NaturalDual.Space →ₗ[ZMod 2] (ZMod 2 × ZMod 2) := {
    toFun x := (f x.1,x.2 v)
    map_add' x y := by ext <;> simp
    map_smul' c x := by ext <;> simp }
  let N := ambientSubmodule W₀ (π.comp E.toLinearMap).ker
  have hgen := (ambientPlane_le_iff W₀ E v f U).mp le_rfl
  have hcomm : ⁅W₀,R⁆ ≤ N := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro r hr x hx
    have hrLC : r ∈ L ⊓ centralizer (U : Set G) := map_subtype_le _ hr
    let l : L := ⟨r,hrLC.1⟩
    let n := W₀.normalizerMonoidHom.rangeRestrict (inclusion hLN l)
    have hfix (z : NaturalDual.Space) (hz : ((E.symm z).toMul : G) ∈ U) :
        NaturalDual.action (q l) z = z := by
      have he : automizerRepresentation W₀ n (E.symm z) = E.symm z := by
        apply Additive.toMul.injective
        apply Subtype.ext
        change r * ((E.symm z).toMul : G) * r⁻¹ = ((E.symm z).toMul : G)
        rw [← hrLC.2 _ hz,mul_inv_cancel_right]
      have hh := hE l (E.symm z)
      rw [he,E.apply_symm_apply] at hh
      exact hh.symm
    have hgv : BinaryLinearThree.W (q l) v = v := congrArg Prod.fst (hfix (v,0) hgen.1)
    have hgf : BinaryLinearThree.W.dual (q l) f = f := congrArg Prod.snd (hfix (0,f) hgen.2)
    have hgi : BinaryLinearThree.W (q l)⁻¹ v = v := by
      have hh := congrArg (BinaryLinearThree.W (q l)⁻¹) hgv
      rw [Representation.inv_self_apply] at hh
      exact hh.symm
    have hπ (z : NaturalDual.Space) : π (NaturalDual.action (q l) z) = π z := by
      apply Prod.ext
      · change f (BinaryLinearThree.W (q l) z.1) = f z.1
        calc
          f (BinaryLinearThree.W (q l) z.1) =
              BinaryLinearThree.W.dual (q l) f (BinaryLinearThree.W (q l) z.1) :=
            congrArg (fun k : Module.Dual (ZMod 2) Vector => k (BinaryLinearThree.W (q l) z.1)) hgf.symm
          _ = f z.1 := by
            change f (BinaryLinearThree.W (q l)⁻¹ (BinaryLinearThree.W (q l) z.1)) = f z.1
            rw [Representation.inv_self_apply]
      · change z.2 (BinaryLinearThree.W (q l)⁻¹ v) = z.2 v
        rw [hgi]
    let y : Additive W₀ := Additive.ofMul ⟨x,hx⟩
    let z := automizerRepresentation W₀ n y - y
    refine ⟨z.toMul,?_,?_⟩
    · change π (E (automizerRepresentation W₀ n y - y)) = 0
      rw [map_sub,hE,map_sub,hπ,sub_self]
    · change (r * x * r⁻¹) / x = ⁅r,x⁆
      rw [div_eq_mul_inv]
      rfl
  rw [Subgroup.disjoint_def]
  intro x hxU hxR
  obtain ⟨u,hu,rfl⟩ := hxU
  obtain ⟨z,hz,he⟩ := hcomm hxR
  have he' : z = u := Subtype.ext he
  subst z
  change π (E (Additive.ofMul u)) = 0 at hz
  change E (Additive.ofMul u) ∈ pairedPlane v f at hu
  obtain ⟨c,d,hcd⟩ := Submodule.mem_span_pair.mp hu
  have hc : c = 0 := by
    have hh := congrArg Prod.fst hz
    rw [← hcd] at hh
    simpa [π,hfv] using hh
  have hd : d = 0 := by
    have hh := congrArg Prod.snd hz
    rw [← hcd] at hh
    simpa [π,hfv] using hh
  have hu0 : Additive.ofMul u = 0 := E.injective (by simpa [hc,hd] using hcd.symm)
  exact congrArg (fun y : Additive W₀ => (y.toMul : G)) hu0

/-- The original moving subgroup has order sixteen once its source supplement
identity is supplied. -/
theorem pairedPlane_residual_card
    {G : Type*} [_root_.Group G] [Finite G] (W₀ L : Subgroup G) [IsElementaryAbelian 2 W₀]
    (hLN : L ≤ normalizer (W₀ : Set G)) (q : L →* BinaryLinearThree.Group)
    (E : Additive W₀ ≃ₗ[ZMod 2] NaturalDual.Space)
    (hE : ∀ l w, E (automizerRepresentation W₀
      (W₀.normalizerMonoidHom.rangeRestrict (inclusion hLN l)) w) =
        NaturalDual.action (q l) (E w))
    (v : Vector) (f : Module.Dual (ZMod 2) Vector) (hfv : f v = 1)
    (hgen : ambientPlane W₀ E v f ⊔ ⁅W₀,localResidual L (ambientPlane W₀ E v f)⁆ = W₀) :
    Nat.card (⁅W₀,localResidual L (ambientPlane W₀ E v f)⁆ : Subgroup G) = 16 := by
  let U := ambientPlane W₀ E v f
  let A := ⁅W₀,localResidual L U⁆
  have hAW : A ≤ W₀ := le_normalizer_iff_commutator_le_left.mp
    ((map_subtype_le _).trans (inf_le_left.trans hLN))
  have hn : A ≤ normalizer (U : Set G) := hAW.trans
    (((le_centralizer W₀).trans (centralizer_le (ambientPlane_le_orbit W₀ E v f))).trans
      (Subgroup.centralizer_le_normalizer _))
  have hc := card_sup_eq_mul_of_normalizes_of_disjoint U A hn
    (pairedPlane_residual_disjoint W₀ L hLN q E hE v f hfv)
  have hW : Nat.card W₀ = 64 := by
    change Nat.card (Additive W₀) = 64
    rw [Nat.card_congr E.toEquiv,Module.natCard_eq_pow_finrank (K := ZMod 2)]
    norm_num [NaturalDual.Space,Module.finrank_prod,BinaryLinearThree.Vector,Matrix.PSL3Two.Fano.Vector]
  change Nat.card (U ⊔ A : Subgroup G) = Nat.card U * Nat.card A at hc
  rw [hgen,hW,DoubledBinaryPlaneQuotient.ambientPlane_card W₀ E v f hfv] at hc
  change Nat.card A = 16
  omega


open Theory.GroupTheory
/-- In a strongly quasithin group every residual moving subgroup normalizes
each ordinary component. The actual component orbit has at most two points. -/
theorem residual_movement_normalizes_component
    {G : Type*} [_root_.Group G] [Finite G] (H W₀ R K : Subgroup G)
    (hQ : CFSG.Quasithin.IsStronglyQuasithin H) (hK : IsComponentIn K H)
    (hWH : W₀ ≤ H) (hRH : R ≤ H) (hR : IsPPerfect 2 R) :
    ⁅W₀,R⁆ ≤ normalizer (K : Set G) := by
  let N := normalizer (K.subgroupOf H : Set H)
  have hinner : ⁅W₀.subgroupOf H,R.subgroupOf H⁆ ≤ N := by
    rcases hK.2.normal_or_index_two_of_odd_rank_le_two hQ with hn | hi
    · let := hn
      rw [show N = normalizer (K.subgroupOf H : Set H) from rfl,normalizer_eq_top]
      exact le_top
    · let : N.Normal := N.normal_of_index_eq_two hi
      have hp : IsPGroup 2 (H ⧸ N) := IsPGroup.of_card (n := 1) (by
        change N.index = 2 ^ 1
        simpa only [pow_one] using hi)
      have hRN : R.subgroupOf H ≤ N :=
        (le_pResidual_of_isPPerfect _ (hR.of_surjective
          (subgroupOfEquivOfLe hRH).symm.toMonoidHom
          (subgroupOfEquivOfLe hRH).symm.surjective)).trans (sInf_le ⟨inferInstance,hp⟩)
      exact (commutator_mono le_rfl hRN).trans (commutator_le_right _ _)
  have hh := map_mono (f := H.subtype) hinner
  rw [map_commutator,map_subgroupOf_eq_of_le hWH,map_subgroupOf_eq_of_le hRH] at hh
  have he : N = (normalizer (K : Set G)).subgroupOf H := (subgroupOf_normalizer_eq hK.1).symm
  exact hh.trans (by
    rw [he]
    rintro x ⟨y,hy,rfl⟩
    exact hy)


/-- The literal induced automizer retains the moving actor's order when
its centralizer kernel is trivial. -/
theorem faithful_inducedAutomizer_card
    {G : Type*} [_root_.Group G] (K A : Subgroup G)
    (hAN : A ≤ normalizer (K : Set G))
    (hker : A ⊓ centralizer (K : Set G) = ⊥) :
    Nat.card (inducedAutomizer K A) = Nat.card A := by
  unfold inducedAutomizer
  rw [← relIndex_ker,MonoidHom.ker_rangeRestrict,normalizerMonoidHom_ker,
    relIndex_subgroupOf hAN,← inf_relIndex_right,inf_comm,hker,relIndex_bot_left]


end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryIntersection
