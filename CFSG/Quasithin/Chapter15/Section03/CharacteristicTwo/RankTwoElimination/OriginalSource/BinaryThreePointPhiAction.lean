module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointPhiKernel
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreeOriginalCoreSections
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointBinaryFixedSpan
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCenter.DistanceEightCenter
public import Theory.Representation.PSL3Two.NaturalDualCentralizer
public import Theory.GroupAction.SubgroupQuotientFullAction
public import Theory.GroupTheory.CommutatorQuotientHom

/-!
# The original point kernel acts on the Frattini layer through the four

The common natural and dual markings control the actual normalizer action
on Z(Q)/H and Phi(Q)/Z(Q). Their invertible commutants are trivial, and
there is no equivariant map from the dual factor to the natural factor.
Consequently [N,Phi(Q)] lies in H for the original point kernel N.
No splitting of Phi(Q)/H or invariance under the whole point centralizer
is used. The source is MS93(4.5)(iii)--(v), printed p.895, with the original
characteristic sections transported through the fixed join embedding.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource CoreActions Extension.SourceCases ChapterC BinaryMS.MS93
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
local notation "sCenter" => CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn
universe u
variable {G : Type u} [Group G]

private theorem marked_coordinates
    {A V : Type*} [Group A] [AddCommGroup V] [Module (ZMod 2) V]
    {L D Z : Subgroup G} {a : L →* A} {σ : Representation (ZMod 2) A V}
    (hs : HasSectionModel L D Z a σ) :
    ∃ p : D →* Multiplicative V, Function.Surjective p ∧ p.ker = Z.subgroupOf D ∧
      ∀ l : L, ∀ x : D,
        (p (D.normalizerMonoidHom (inclusion hs.2.1 l) x)).toAdd =
          σ (a l) (p x).toAdd := by
  obtain ⟨_,_,_,hn,e,he⟩ := hs
  let := hn
  let p := e.toMonoidHom.comp (QuotientGroup.mk' (Z.subgroupOf D))
  refine ⟨p,e.surjective.comp (QuotientGroup.mk'_surjective _),?_,?_⟩
  · rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  · intro l x
    exact he l x _ rfl

private theorem section_commutant_bound
    {A V : Type*} [Group A] [AddCommGroup V] [Module (ZMod 2) V]
    {L D Z R : Subgroup G} {a : L →* A} {σ : Representation (ZMod 2) A V}
    (hs : HasSectionModel L D Z a σ) (ha : Function.Surjective a)
    (hRD : R ≤ normalizer D) (hRZ : R ≤ normalizer Z)
    (hcomm : ⁅⁅R,L⁆,D⁆ ≤ Z)
    (htriv : ∀ f : V ≃ₗ[ZMod 2] V,
      (∀ g v, f (σ g v) = σ g (f v)) → f = LinearEquiv.refl _ _) :
    ⁅R,D⁆ ≤ Z := by
  obtain ⟨_,hLD,hLZ,hn,e,he⟩ := hs
  let := hn
  let P := R ⊔ L
  have hPD : P ≤ normalizer D := sup_le hRD hLD
  have hPZ : P ≤ normalizer Z := sup_le hRZ hLZ
  obtain ⟨β,hβ⟩ := exists_quotient_conjugation_action P D Z hPD hPZ hn
  let γ : P →* MulAut (Multiplicative V) := (MulAut.congr e).toMonoidHom.comp β
  let p : D →* Multiplicative V := e.toMonoidHom.comp (QuotientGroup.mk' (Z.subgroupOf D))
  have hp : Function.Surjective p := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hγ (r : P) (x : D) :
      γ r (p x) = p (D.normalizerMonoidHom (inclusion hPD r) x) := by
    change e (β r (e.symm (e (QuotientGroup.mk' _ x)))) = _
    rw [e.symm_apply_apply,hβ]
    rfl
  have hk : (⁅R,L⁆).subgroupOf P ≤ β.ker :=
    quotient_conjugation_action_kills_commutator_layer P D Z ⁅R,L⁆ hn hPD
      (by rwa [commutator_comm D]) β hβ
  have hco (r : R) (l : L) : Commute (γ (inclusion le_sup_left r)) (γ (inclusion le_sup_right l)) := by
    apply commutatorElement_eq_one_iff_mul_comm.mp
    rw [←map_commutatorElement]
    have hb : β ⁅inclusion (show R ≤ P from le_sup_left) r,
        inclusion (show L ≤ P from le_sup_right) l⁆ = 1 :=
      hk (commutator_mem_commutator r.property l.property)
    change MulAut.congr e (β _) = 1
    rw [hb,map_one]
  have hγL (l : L) (v : V) :
      (γ (inclusion (show L ≤ P from le_sup_right) l) (Multiplicative.ofAdd v)).toAdd = σ (a l) v := by
    obtain ⟨x,hx⟩ := hp (Multiplicative.ofAdd v)
    have hv : (p x).toAdd = v := congrArg Multiplicative.toAdd hx
    rw [←hv]
    change (γ (inclusion le_sup_right l) (p x)).toAdd = σ (a l) (p x).toAdd
    rw [hγ]
    change (e (QuotientGroup.mk' _
      (D.normalizerMonoidHom (inclusion hPD (inclusion le_sup_right l)) x))).toAdd =
        σ (a l) (e (QuotientGroup.mk' _ x)).toAdd
    exact he l x _ rfl
  have hfix (r : R) (v : V) :
      γ (inclusion (show R ≤ P from le_sup_left) r) (Multiplicative.ofAdd v) = Multiplicative.ofAdd v := by
    let f₀ : V ≃+ V := AddEquiv.toMultiplicative.symm (γ (inclusion le_sup_left r))
    let f : V ≃ₗ[ZMod 2] V := { f₀ with map_smul' := ZMod.map_smul f₀ }
    have hf := htriv f (by
      intro g v
      obtain ⟨l,rfl⟩ := ha g
      have hh := congrArg Multiplicative.toAdd
        (DFunLike.congr_fun (hco r l).eq (Multiplicative.ofAdd v))
      change (γ (inclusion le_sup_left r)
          (γ (inclusion le_sup_right l) (Multiplicative.ofAdd v))).toAdd =
        (γ (inclusion le_sup_right l)
          (γ (inclusion le_sup_left r) (Multiplicative.ofAdd v))).toAdd at hh
      change (γ (inclusion le_sup_left r) (Multiplicative.ofAdd (σ (a l) v))).toAdd =
        σ (a l) (γ (inclusion le_sup_left r) (Multiplicative.ofAdd v)).toAdd
      rw [←hγL l v,←hγL l _]
      exact hh)
    exact congrArg (fun f : V ≃ₗ[ZMod 2] V => Multiplicative.ofAdd (f v)) hf
  apply commutator_le.mpr
  intro r hr x hx
  let x' := D.normalizerMonoidHom (inclusion hRD ⟨r,hr⟩) ⟨x,hx⟩
  have heq : p x' = p ⟨x,hx⟩ :=
    (hγ (inclusion le_sup_left ⟨r,hr⟩) ⟨x,hx⟩).symm.trans (hfix ⟨r,hr⟩ _)
  have heq' : QuotientGroup.mk' (Z.subgroupOf D) x' = QuotientGroup.mk' (Z.subgroupOf D) ⟨x,hx⟩ :=
    e.injective heq
  have hh := QuotientGroup.eq_iff_div_mem.mp heq'
  change (r * x * r⁻¹) / x ∈ Z at hh
  simpa only [commutatorElement_def,div_eq_mul_inv] using hh

private theorem scalar_aut_trivial {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [Nontrivial V] (f : V ≃ₗ[ZMod 2] V)
    (hs : ∃ c : ZMod 2, ∀ v, f v = c • v) : f = LinearEquiv.refl _ _ := by
  obtain ⟨c,hc⟩ := hs
  have hb : c = 0 ∨ c = 1 := (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c
  have hc1 : c = 1 := hb.resolve_left (by
    intro hz
    obtain ⟨v,hv⟩ := exists_ne (0 : V)
    exact hv (f.injective (by rw [hc,hz,zero_smul,map_zero])))
  ext v
  rw [hc,hc1,one_smul]
  rfl

private theorem natural_trivial_commutant
    (f : BinaryLinearThree.Vector ≃ₗ[ZMod 2] BinaryLinearThree.Vector)
    (hf : ∀ g v, f (BinaryLinearThree.W g v) = BinaryLinearThree.W g (f v)) :
    f = LinearEquiv.refl _ _ := by
  apply scalar_aut_trivial f
  exact BinaryLinearThree.NaturalDual.natural_scalar
    ⟨f.toLinearMap,fun g => LinearMap.ext (hf g)⟩

private theorem dual_trivial_commutant
    (f : Module.Dual (ZMod 2) BinaryLinearThree.Vector ≃ₗ[ZMod 2]
      Module.Dual (ZMod 2) BinaryLinearThree.Vector)
    (hf : ∀ g v, f (BinaryLinearThree.W.dual g v) = BinaryLinearThree.W.dual g (f v)) :
    f = LinearEquiv.refl _ _ := by
  apply scalar_aut_trivial f
  exact BinaryLinearThree.NaturalDual.dual_scalar
    ⟨f.toLinearMap,fun g => LinearMap.ext (hf g)⟩

private theorem natural_dual_section_bound
    {L D Z H R : Subgroup G} (a : L →* BinaryLinearThree.Group)
    (ha : Function.Surjective a)
    (sn : HasSectionModel L Z H a BinaryLinearThree.W)
    (sd : HasSectionModel L D Z a BinaryLinearThree.W.dual)
    (hZD : Z ≤ centralizer (D : Set G))
    (hRD : R ≤ normalizer D) (hRZ : R ≤ normalizer Z) (hRH : R ≤ normalizer H)
    (hcomm : ⁅⁅R,L⁆,D⁆ ≤ H) : ⁅R,D⁆ ≤ H := by
  have hZH := section_commutant_bound sn ha hRZ hRH
    ((commutator_mono le_rfl sd.1).trans hcomm) natural_trivial_commutant
  have hDZ := section_commutant_bound sd ha hRD hRZ
    (hcomm.trans sn.1) dual_trivial_commutant
  obtain ⟨pn,hpn,hkn,hen⟩ := marked_coordinates sn
  obtain ⟨pd,hpd,hkd,hed⟩ := marked_coordinates sd
  have hHD : H ≤ D := sn.1.trans sd.1
  have hDH : D ≤ normalizer H :=
    (le_centralizer_iff.mp (sn.1.trans hZD)).trans (Subgroup.centralizer_le_normalizer _)
  have hn : (H.subgroupOf D).Normal := (normal_subgroupOf_iff_le_normalizer hHD).mpr hDH
  let := hn
  let P := R ⊔ L
  have hPD : P ≤ normalizer D := sup_le hRD sd.2.1
  have hPH : P ≤ normalizer H := sup_le hRH sn.2.2.1
  obtain ⟨β,hβ⟩ := exists_quotient_conjugation_action P D H hPD hPH hn
  let π := QuotientGroup.mk' (H.subgroupOf D)
  let j : Z →* (D ⧸ H.subgroupOf D) := π.comp (inclusion sd.1)
  have hj (x y : Z) (hh : j x = j y) : pn x = pn y := by
    have hm : inclusion sd.1 x / inclusion sd.1 y ∈ H.subgroupOf D :=
      QuotientGroup.eq_iff_div_mem.mp hh
    have hz : x / y ∈ pn.ker := by rw [hkn]; exact hm
    have hz' : pn x / pn y = 1 := by simpa only [map_div] using (MonoidHom.mem_ker.mp hz)
    exact div_eq_one.mp hz'
  have hk : (⁅R,L⁆).subgroupOf P ≤ β.ker :=
    quotient_conjugation_action_kills_commutator_layer P D H ⁅R,L⁆ hn hPD
      (by rwa [commutator_comm D]) β hβ
  have hco (r : R) (l : L) : Commute (β (inclusion le_sup_left r)) (β (inclusion le_sup_right l)) := by
    apply commutatorElement_eq_one_iff_mul_comm.mp
    rw [←map_commutatorElement]
    exact hk (commutator_mem_commutator r.property l.property)
  apply commutator_le.mpr
  intro r hr x hx
  let δ : D →* Z := {
    toFun y := ⟨⁅(y : G),r⁆,(by rw [commutator_comm] at hDZ; exact hDZ (commutator_mem_commutator y.property hr))⟩
    map_one' := Subtype.ext (by simp)
    map_mul' y w := by
      apply Subtype.ext
      change ⁅(y : G) * w,r⁆ = ⁅(y : G),r⁆ * ⁅(w : G),r⁆
      have hw : ⁅(w : G),r⁆ ∈ Z := by
        rw [commutator_comm] at hDZ
        exact hDZ (commutator_mem_commutator w.property hr)
      have hy : ⁅(y : G),r⁆ ∈ Z := by
        rw [commutator_comm] at hDZ
        exact hDZ (commutator_mem_commutator y.property hr)
      rw [commutatorElement_mul_left_eq_conj_mul,
        hZD hw y y.property,mul_inv_cancel_right]
      exact (hZD hw _ (sd.1 hy)).symm }
  let f := pn.comp δ
  have hker : pd.ker ≤ f.ker := by
    intro y hy
    have hyZ : (y : G) ∈ Z := by rw [hkd] at hy; exact hy
    have hh : (δ y : G) ∈ H := by
      rw [commutator_comm] at hZH
      exact hZH (commutator_mem_commutator hyZ hr)
    exact (show δ y ∈ pn.ker from hkn ▸ hh)
  let q := pd.liftOfSurjective hpd ⟨f,hker⟩
  have hq (y : D) : q (pd y) = pn (δ y) := by simp [q,f]
  have hδ (y : D) : j (δ y) = π y * β (inclusion le_sup_left ⟨r,hr⟩) (π y⁻¹) := by
    change π (inclusion sd.1 (δ y)) = _
    rw [hβ,←map_mul]
    congr 1
    apply Subtype.ext
    change ⁅(y : G),r⁆ = (y : G) * (r * (y : G)⁻¹ * r⁻¹)
    simp only [commutatorElement_def,mul_assoc]
  have heδ (l : L) (y : D) :
      pn (δ (D.normalizerMonoidHom (inclusion sd.2.1 l) y)) =
        pn (Z.normalizerMonoidHom (inclusion sn.2.1 l) (δ y)) := by
    apply hj
    have hleft (v : D) : π (D.normalizerMonoidHom (inclusion sd.2.1 l) v) =
        β (inclusion le_sup_right l) (π v) := (hβ (inclusion le_sup_right l) v).symm
    have hright : j (Z.normalizerMonoidHom (inclusion sn.2.1 l) (δ y)) =
        β (inclusion le_sup_right l) (j (δ y)) := (hβ (inclusion le_sup_right l) (inclusion sd.1 (δ y))).symm
    rw [hright,hδ,hδ,map_mul,hleft]
    congr 1
    rw [←map_inv,hleft,map_inv]
    exact DFunLike.congr_fun (hco ⟨r,hr⟩ l).eq _
  let ql := (AddMonoidHom.toMultiplicative.symm q).toZModLinearMap 2
  let T : BinaryLinearThree.W.dual.IntertwiningMap BinaryLinearThree.W := {
    toLinearMap := ql
    isIntertwining' g := by
      apply LinearMap.ext
      intro v
      obtain ⟨l,rfl⟩ := ha g
      obtain ⟨y,hy⟩ := hpd (Multiplicative.ofAdd v)
      have hd := hed l y
      have hn := hen l (δ y)
      have hconj := congrArg Multiplicative.toAdd (heδ l y)
      change ql (BinaryLinearThree.W.dual (a l) v) = BinaryLinearThree.W (a l) (ql v)
      have hv : (pd y).toAdd = v := congrArg Multiplicative.toAdd hy
      rw [←hv,←hd]
      change (q (pd (D.normalizerMonoidHom (inclusion sd.2.1 l) y))).toAdd =
        BinaryLinearThree.W (a l) (q (pd y)).toAdd
      rw [hq,hq]
      exact hconj.trans hn }
  have hz := congrArg (fun T : BinaryLinearThree.W.dual.IntertwiningMap BinaryLinearThree.W =>
    T (pd ⟨x,hx⟩).toAdd) (BinaryLinearThree.NaturalDual.dual_natural_zero T)
  have hz' : pn (δ ⟨x,hx⟩) = 1 := by
    change (q (pd ⟨x,hx⟩)).toAdd = 0 at hz
    rw [hq] at hz
    exact hz
  have hh : ⁅x,r⁆ ∈ H := by
    have hmem : δ ⟨x,hx⟩ ∈ pn.ker := hz'
    rw [hkn] at hmem
    exact hmem
  simpa only [commutatorElement_inv] using H.inv_mem hh

private theorem section_of_complement
    {A V : Type*} [Group A] [AddCommGroup V] [Module (ZMod 2) V]
    {L Z H U : Subgroup G} {a : L →* A} {σ : Representation (ZMod 2) A V}
    (hs : HasSectionModel L U ⊥ a σ) (hZ : Z = U ⊔ H)
    (hdis : U ⊓ H = ⊥) (hZH : Z ≤ normalizer H)
    (hLZ : L ≤ normalizer Z) (hLH : L ≤ normalizer H) :
    HasSectionModel L Z H a σ := by
  have hUZ : U ≤ Z := hZ ▸ le_sup_left
  have hHZ : H ≤ Z := hZ ▸ le_sup_right
  have hn : (H.subgroupOf Z).Normal := (normal_subgroupOf_iff_le_normalizer hHZ).mpr hZH
  let := hn
  let π := QuotientGroup.mk' (H.subgroupOf Z)
  let f := π.comp (inclusion hUZ)
  have hfi : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply _root_.eq_bot_iff.mpr
    intro u hu
    have huH : (u : G) ∈ H := (QuotientGroup.eq_one_iff (inclusion hUZ u)).mp hu
    have hu1 : (u : G) = 1 := hdis.le ⟨u.property,huH⟩
    exact Subtype.ext hu1
  have hfs : Function.Surjective f := by
    intro x
    obtain ⟨z,rfl⟩ := QuotientGroup.mk'_surjective (H.subgroupOf Z) x
    have hz : (z : G) ∈ (U : Set G) * (H : Set G) := by
      rw [←coe_mul_of_left_le_normalizer_right U H (hUZ.trans hZH),←hZ]
      exact z.property
    obtain ⟨u,hu,h,hh,he⟩ := hz
    refine ⟨⟨u,hu⟩,?_⟩
    apply QuotientGroup.eq_iff_div_mem.mpr
    change u / (z : G) ∈ H
    rw [←he]
    have hconj : u * h⁻¹ * u⁻¹ ∈ H :=
      (mem_normalizer_iff.mp (hZH (hUZ hu)) h⁻¹).mp (H.inv_mem hh)
    simpa only [div_eq_mul_inv,mul_inv_rev,mul_assoc] using hconj
  obtain ⟨p,hp,hk,he⟩ := marked_coordinates hs
  have hpi : Function.Injective p := (MonoidHom.ker_eq_bot_iff p).mp (by rw [hk,bot_subgroupOf])
  let ef := MulEquiv.ofBijective f ⟨hfi,hfs⟩
  let ep := MulEquiv.ofBijective p ⟨hpi,hp⟩
  let e := ef.symm.trans ep
  have hef (u : U) : e (f u) = p u := by
    change ep (ef.symm (ef u)) = p u
    rw [ef.symm_apply_apply]
    rfl
  refine ⟨hHZ,hLZ,hLH,hn,e,?_⟩
  intro l x y hy
  obtain ⟨u,hu⟩ := hfs (π x)
  obtain ⟨β,hβ⟩ := exists_quotient_conjugation_action L Z H hLZ hLH hn
  have hyq : π y = β l (π x) := by
    rw [hβ]
    congr 1
    exact Subtype.ext hy
  have heq : π y = f (U.normalizerMonoidHom (inclusion hs.2.1 l) u) := by
    rw [hyq,←hu]
    exact hβ l (inclusion hUZ u)
  change (e (π y)).toAdd = σ (a l) (e (π x)).toAdd
  rw [heq,←hu,hef,hef]
  exact he l u

set_option maxHeartbeats 600000 in
private theorem original_marked_pair [Finite G]
    (d : LocalData G) (L : Subgroup G)
    (b : BinaryMS.Input KnownSimple.IsKnownSimple
      (L.subgroupOf (L ⊔ d.S)) (d.S.subgroupOf (L ⊔ d.S)))
    (t : InputSetup b) (common : CommonFacts t.reduction.radical t.source t.geometry)
    (hb : 4 < t.geometry.b t.reduction.radical)
    (hfixed : core t.reduction.radical
        (alpha t.reduction.radical) ⊓ centralizer
          (Ltilde t.reduction.radical
            (alpha t.reduction.radical) :
              Set (FreeAmalgam t.reduction.radical)) =
      H t.reduction.radical
        (alpha t.reduction.radical))
    (hF : coreFixed L = intrinsicFour L) :
    ∃ e' : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL,
      HasSectionModel L (sCenter (LinearThree.commutatorCore L)) (intrinsicFour L)
        (linearThreeActor e') BinaryLinearThree.W ∧
      HasSectionModel L (frattiniIn (LinearThree.commutatorCore L))
        (sCenter (LinearThree.commutatorCore L)) (linearThreeActor e') BinaryLinearThree.W.dual := by
  let J := L ⊔ d.S
  let Q := LinearThree.commutatorCore L
  have hQJ : Q ≤ J := (LinearThree.commutatorCore_le L).trans ((map_subtype_le _).trans le_sup_left)
  have hQ0 : msQ (L.subgroupOf J) (d.S.subgroupOf J) = Q.subgroupOf J := by
    apply map_injective J.subtype_injective
    have hms : msQ (L.subgroupOf J) (d.S.subgroupOf J) = BinaryMS.commutatorCore (L.subgroupOf J) := by
      have hp : (⊤ : Subgroup J).pCoreIn 2 = pCore 2 J := pCore_map_iso 2 topEquiv
      rw [msQ,b.sup_eq_top,hp]
    rw [hms,map_subgroupOf_eq_of_le hQJ]
    exact sourceQ_map_subtype (show L ≤ J from le_sup_left) b.component
  let Q₀ := msQ (L.subgroupOf J) (d.S.subgroupOf J)
  let Z₀ := sCenter Q₀
  let F₀ := Q₀ ⊓ centralizer (L.subgroupOf J : Set J)
  let U₀ := ⁅Z₀,L.subgroupOf J⁆
  obtain ⟨hZe,hZ,hdis,hs⟩ := t.center_source_sections common hb
  have hZn : (L.subgroupOf J) ≤ normalizer Z₀ := by
    have hLQ : L.subgroupOf J ≤ normalizer Q₀ := by
      change L.subgroupOf J ≤ normalizer (⁅(L.subgroupOf J ⊔ d.S.subgroupOf J).pCoreIn 2,L.subgroupOf J⁆ : Subgroup J)
      exact normalizer_commutator_ge_right _ _
    exact hLQ.trans (normalizer_le_normalizer_characteristic_image Q₀ (center Q₀))
  have hLF : L.subgroupOf J ≤ normalizer F₀ :=
    (le_centralizer_iff.mp inf_le_right).trans (Subgroup.centralizer_le_normalizer _)
  have hZF : Z₀ ≤ normalizer F₀ := by
    have hc : Z₀ ≤ centralizer (Q₀ : Set J) := by
      rintro _ ⟨z,hz,rfl⟩ x hx
      exact congrArg Subtype.val (mem_center_iff.mp hz ⟨x,hx⟩)
    exact (hc.trans (centralizer_le inf_le_left)).trans (Subgroup.centralizer_le_normalizer _)
  have hn := section_of_complement hs (hZ.trans (sup_comm _ _))
    ((inf_comm _ _).trans hdis) hZF hZn hLF
  have hd := t.frattini_sectionModel_of_fixedFactor common hb hfixed
  have hF0 : F₀ = (intrinsicFour L).subgroupOf J := by
    change Q₀ ⊓ centralizer (L.subgroupOf J : Set J) = _
    rw [show Q₀ = Q.subgroupOf J from hQ0,←hF]
    ext x
    change ((x : G) ∈ Q ∧ x ∈ centralizer (L.subgroupOf J : Set J)) ↔
      ((x : G) ∈ Q ∧ (x : G) ∈ centralizer (L : Set G))
    constructor
    · rintro ⟨hq,hc⟩
      exact ⟨hq,fun y hy => congrArg Subtype.val (hc ⟨y,(show L ≤ J from le_sup_left) hy⟩ hy)⟩
    · rintro ⟨hq,hc⟩
      exact ⟨hq,fun y hy => Subtype.ext (hc y hy)⟩
  change HasSectionModel (L.subgroupOf J) (sCenter Q₀) F₀ _ _ at hn
  rw [hF0] at hn
  dsimp only [Q₀] at hn
  rw [hQ0,centerIn_subgroupOf hQJ] at hn
  change HasSectionModel (L.subgroupOf J) (frattiniIn Q₀) (sCenter Q₀) _ _ at hd
  dsimp only [Q₀] at hd
  rw [hQ0,frattiniIn_subgroupOf hQJ,centerIn_subgroupOf hQJ] at hd
  let i := subgroupOfEquivOfLe (show L ≤ J from le_sup_left)
  let c := QuotientGroup.congr _ _ i.symm (pCore_map_iso 2 i.symm)
  let em := b.quotientEquiv.trans common.natural.marking
  let e' := c.trans em
  let a := linearThreeActor e'
  have hactor : linearThreeActor em = a.comp i.toMonoidHom := by
    apply MonoidHom.ext
    intro x
    change em (QuotientGroup.mk' _ x) = em (c (QuotientGroup.mk' _ (i x)))
    change em (QuotientGroup.mk' _ x) = em (QuotientGroup.mk' _ (i.symm (i x)))
    rw [i.symm_apply_apply]
  rw [hactor] at hn hd
  have hZJ : sCenter Q ≤ J := (map_subtype_le _).trans hQJ
  have hHJ : intrinsicFour L ≤ J :=
    ((show intrinsicFour L ≤ Q from
      (commutator_mono (commutator_le_self Q) le_rfl).trans (commutator_le_self Q))).trans hQJ
  exact ⟨e',HasSectionModel.of_subgroupOf le_sup_left hZJ hHJ a _ hn,
    HasSectionModel.of_subgroupOf le_sup_left ((map_subtype_le _).trans hQJ) hZJ a _ hd⟩


variable [Finite G]

/-- The actual original point kernel moves the Frattini layer only into the intrinsic four. -/
theorem binary_three_source_point_phi_action
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (e : (c.L ⧸ pCore 2 c.L) ≃* PSL(3,ZMod 2))
    (b : BinaryMS.Input KnownSimple.IsKnownSimple
      (c.L.subgroupOf (c.L ⊔ d.S)) (d.S.subgroupOf (c.L ⊔ d.S)))
    (t : InputSetup b)
    (hc : ¬ IsMulCommutative (BinaryMS.commutatorCore (c.L.subgroupOf (c.L ⊔ d.S))))
    (hb : 4 < t.geometry.b t.reduction.radical)
    (z : G) (hLS : c.L ⊔ d.S ≤ centralizer ({z} : Set G))
    (P : Sylow 2 (centralizer ({z} : Set G)))
    (hP : (P : Subgroup _).map (centralizer ({z} : Set G)).subtype = d.S)
    : let C := centralizer ({z} : Set G)
      let N := C.pCoreIn 2
      let Phi := frattiniIn (LinearThree.commutatorCore c.L)
      ⁅N,sCenter (LinearThree.commutatorCore c.L)⁆ ≤ intrinsicFour c.L ∧
        ⁅N,Phi⁆ ≤ intrinsicFour c.L := by
  obtain ⟨hW,hJ,hcore,_⟩ := source_lemma_15_3_16_local_geometry
    hG d hempty hM hu hmany hI htwo hf c
  obtain ⟨hne,hBaum,_⟩ := InitialSource.UniformControl.source_controls_of_ordering_maximal
    hG d.T hempty hM hu hmany (d.action.card_centralInvolutions d.T d.sylow_le)
  let eSL := e.trans (BinaryLinear.OuterCyclic.projectiveEquivSL (by decide))
  obtain ⟨_,h,hg⟩ := residual_geometry_of_original hG d hempty hM hu hmany hne hBaum
    hI c (OutsideStructure.rankTwoCase_three_rank hG d hI htwo) eSL hW hJ hcore
  obtain ⟨common⟩ := t.commonFacts hc
  have earlier := DistanceEight.PathCentrality.Source44.OriginalEarlier.earlier common hb
  have hnot : ¬ (d.T : Subgroup G) ≤ d.S := by
    intro hTS
    have ht : d.S.subgroupOf (d.T : Subgroup G) = ⊤ := top_unique (fun x _ => hTS x.property)
    have hi := d.action.planeStabilizer_index_two d.T d.sylow_le 1
    rw [ht,index_top] at hi
    omega
  obtain ⟨g,hgT,hgS⟩ := SetLike.not_le_iff_exists.mp hnot
  have hfixed := source_fixedFactor_eq_H_of_original_exchange
    d c.L eSL h hg b t common earlier g hgT hgS
  have hF := (binary_three_large_distance_fixed_factor_bound
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb).2.1
  obtain ⟨a,sn,sd⟩ := original_marked_pair d c.L b t common hb hfixed hF
  let C := centralizer ({z} : Set G)
  let N := C.pCoreIn 2
  let J := c.L ⊔ d.S
  let Q := LinearThree.commutatorCore c.L
  let Phi := frattiniIn Q
  let ZQ := sCenter Q
  have hJL : J ≤ normalizer c.L :=
    (normal_subgroupOf_iff_le_normalizer (show c.L ≤ J from le_sup_left)).mp b.component_normal
  have hJQ : J ≤ normalizer Q := hJL.trans (normalizer_le_normalizer_commutatorCore c.L)
  have hNS : N ≤ d.S := hP ▸ pCoreIn_le_sylow C P
  have hCN : C ≤ normalizer N := C.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image C (pCore 2 C))
  have hNJ : N ≤ J.pCoreIn 2 := le_pCoreIn_of_normalizes
    (isPGroup_pCoreIn 2 C) (hNS.trans le_sup_right) (hLS.trans hCN)
  have hNL : ⁅N,c.L⁆ ≤ Q := (commutator_mono hNJ le_rfl).trans
    (overgroup_core_commutator_eq d c (le_sup_right.trans hJL)).le
  have hNQ : N ≤ normalizer Q := (hNS.trans le_sup_right).trans hJQ
  have hNPhi : N ≤ normalizer Phi := hNQ.trans
    (normalizer_le_normalizer_characteristic_image Q (frattini Q))
  have hNZQ : N ≤ normalizer ZQ := hNQ.trans
    (normalizer_le_normalizer_characteristic_image Q (center Q))
  have hNH : N ≤ normalizer (intrinsicFour c.L) :=
    ((hNS.trans le_sup_right).trans hJL).trans (intrinsicFour_normalized c.L)
  have hroot : _root_.commutator Q = frattini Q :=
    (binary_three_large_distance_original_core_structure
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb).2.2.2.2.2.1
  have hPhi : Phi = ⁅Q,Q⁆ := by
    dsimp only [Phi,frattiniIn]
    rw [←hroot,_root_.commutator_def,map_commutator,←MonoidHom.range_eq_map,range_subtype]
  have hQPhi : ⁅Q,Phi⁆ = intrinsicFour c.L := by rw [hPhi,commutator_comm]; rfl
  have hZcent : ZQ ≤ centralizer (Phi : Set G) := by
    rintro _ ⟨x,hx,rfl⟩ y hy
    exact congrArg Subtype.val (mem_center_iff.mp hx ⟨y,map_subtype_le _ hy⟩)
  have hact := natural_dual_section_bound (linearThreeActor a)
    (a.surjective.comp (QuotientGroup.mk'_surjective _)) sn sd hZcent
    hNPhi hNZQ hNH ((commutator_mono hNL le_rfl).trans hQPhi.le)
  exact ⟨(commutator_mono le_rfl sd.1).trans hact,hact⟩


/-- The actual C-conjugate span of Phi is in the third center of the point kernel. -/
theorem binary_three_source_binary_phi_span_central
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (e : (c.L ⧸ pCore 2 c.L) ≃* PSL(3,ZMod 2))
    (b : BinaryMS.Input KnownSimple.IsKnownSimple
      (c.L.subgroupOf (c.L ⊔ d.S)) (d.S.subgroupOf (c.L ⊔ d.S)))
    (t : InputSetup b)
    (hc : ¬ IsMulCommutative (BinaryMS.commutatorCore (c.L.subgroupOf (c.L ⊔ d.S))))
    (hb : 4 < t.geometry.b t.reduction.radical)
    (z : G) (hzH : z ∈ LinearThree.OriginalSource.intrinsicFour c.L)
    (hz2 : orderOf z = 2) (hLS : c.L ⊔ d.S ≤ centralizer ({z} : Set G))
    (P : Sylow 2 (centralizer ({z} : Set G)))
    (hP : (P : Subgroup _).map (centralizer ({z} : Set G)).subtype = d.S)
    (K : Subgroup ((centralizer ({z} : Set G)) ⧸ pCore 2 (centralizer ({z} : Set G))))
    [K.Normal]
    (hBK : (c.L.subgroupOf (centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))) ≤ K)
    {n : ℕ} (hn : n = 4 ∨ n = 5) (hm : ClassicalGroup.IsPSL K n 2) :
    let C := centralizer ({z} : Set G)
    let N := C.pCoreIn 2
    let H := intrinsicFour c.L
    let Phi := frattiniIn (LinearThree.commutatorCore c.L)
    let U := conjugateSpanBy H C
    let V := conjugateSpanBy Phi C
    Phi ≤ N ∧ V ≤ N ∧ C ≤ normalizer V ∧ ⁅V,N⁆ ≤ U ∧
      ⁅⁅V,N⁆,N⁆ ≤ zpowers z ∧ ⁅⁅⁅V,N⁆,N⁆,N⁆ = ⊥ ∧
      V.subgroupOf N ≤ Subgroup.upperCentralSeries N 3 := by
  let C := centralizer ({z} : Set G)
  let N := C.pCoreIn 2
  let H := intrinsicFour c.L
  let Phi := frattiniIn (LinearThree.commutatorCore c.L)
  let U := conjugateSpanBy H C
  let V := conjugateSpanBy Phi C
  have hPhi := binary_three_source_binary_phi_kernel
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP K hBK hn hm
  have hact := (binary_three_source_point_phi_action
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP).2
  have hspan := binary_three_source_binary_fixed_span
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP K hBK hn hm
  have hNC : N ≤ C := C.pCoreIn_le 2
  have hCN : C ≤ normalizer N := C.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image C (pCore 2 C))
  have hVN : V ≤ N := conjugateSpanBy_le hPhi hCN
  have hVU : ⁅V,N⁆ ≤ U := by
    rw [commutator_conjugateSpanBy_of_normalized_right Phi C N (hPhi.trans hNC) hCN]
    exact conjugateSpanBy_mono (by rwa [commutator_comm]) le_rfl
  have hUZ : ⁅U,N⁆ ≤ zpowers z := hspan.2.2.2.2.2.1
  have hVZ : ⁅⁅V,N⁆,N⁆ ≤ zpowers z := (commutator_mono hVU le_rfl).trans hUZ
  have hZC : zpowers z ≤ centralizer (C : Set G) := by
    apply zpowers_le.mpr
    intro x hx
    exact mem_centralizer_singleton_iff.mp hx
  have hzero : ⁅⁅⁅V,N⁆,N⁆,N⁆ = ⊥ := _root_.eq_bot_iff.mpr
    ((commutator_mono hVZ le_rfl).trans
      (commutator_eq_bot_iff_le_centralizer.mpr (hZC.trans (centralizer_le hNC))).le)
  refine ⟨hPhi,hVN,le_normalizer_conjugateSpanBy _ _,hVU,hVZ,hzero,?_⟩
  intro v hv
  rw [Subgroup.mem_upperCentralSeries_succ_iff]
  intro n
  rw [Subgroup.mem_upperCentralSeries_succ_iff]
  intro m
  rw [Subgroup.mem_upperCentralSeries_succ_iff]
  intro k
  change ⁅⁅⁅v,n⁆,m⁆,k⁆ = 1
  apply Subtype.ext
  exact hzero.le (commutator_mem_commutator
    (commutator_mem_commutator (commutator_mem_commutator hv n.property) m.property) k.property)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
