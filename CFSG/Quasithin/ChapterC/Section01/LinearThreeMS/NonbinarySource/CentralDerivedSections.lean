module
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.DoubledCenter

/-!
# Central derived and Frattini flags in the doubled-center branch

Every nonzero proper K-invariant subgroup of a doubled natural section is
an actual natural subgroup, and the literal quotient by it is natural at
the same full SL₃ marking. Transport to additive coordinates, classify the
subgroup as a scalar graph, and use its coordinate projection and the
complementary difference map to construct both equivariant isomorphisms.
No field-linearity of the original subgroup is assumed.

A nontrivial relative normal subgroup of a finite two-group meets its central
omega. Applied to a doubled natural whole center, this identifies the center's
intersections with the actual derived and Frattini subgroups: each is the
whole center or has the two natural sections just constructed. In particular,
a nonabelian core has a natural central subgroup in Q' and Φ(Q) with natural
quotient in the whole center. The subgroup need not be invariant under the
entire radical; its normality in Q and normalization by K are retained.

For the genuine MS-pair, the proved doubled-omega reconstruction supplies the
whole center in every nonbinary degree. NonblockCentralDerivedSections applies
the flags to the original source configuration, including field four, with
no additional classification premise. Excluding the doubled nonabelian branch
and recognizing the upper sections remain required for full C.1.34.

Source: Aschbacher–Smith C.1.34, printed pp.136–137, and original 4.3.8–10,
pp.616–617; the normal-subgroup intersection and graph arguments are elementary.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.CentralDerivedSections
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] {K Z A : Subgroup G}
variable {F : Type} [Field F]
local notation "W" => (Fin 3 → F)
local notation "V" => (W × W)

private theorem models_of_projection
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (hAZ : A ≤ Z) (hKZ : K ≤ normalizer (Z : Set G))
    (hKA : K ≤ normalizer (A : Set G))
    (b : Z ≃* Multiplicative V)
    (hb : ∀ (k : K) (x y : Z), (y : G) = k*(x:G)*(k:G)⁻¹ →
      (b y).toAdd = (specialLinearNatural 3 (linearThreeActor e k) (b x).toAdd.1,
        specialLinearNatural 3 (linearThreeActor e k) (b x).toAdd.2))
    (r s : V →+ W)
    (hr : Function.Bijective (fun x : A => r (b (inclusion hAZ x)).toAdd))
    (hs : Function.Surjective s)
    (hk : ∀ x : Z, s (b x).toAdd=0 ↔ (x:G) ∈ A)
    (hre : ∀ g v, r (specialLinearNatural 3 g v.1,specialLinearNatural 3 g v.2)=
      specialLinearNatural 3 g (r v))
    (hse : ∀ g v, s (specialLinearNatural 3 g v.1,specialLinearNatural 3 g v.2)=
      specialLinearNatural 3 g (s v)) :
    HasSectionModel K A ⊥ (linearThreeActor e) (specialLinearNatural 3) ∧
      HasSectionModel K Z A (linearThreeActor e) (specialLinearNatural 3) := by
  let f : A →* Multiplicative W := r.toMultiplicative.comp (b.toMonoidHom.comp (inclusion hAZ))
  let a : A ≃* Multiplicative W := MulEquiv.ofBijective f hr
  have hbottom : HasSectionModel K A ⊥ (linearThreeActor e) (specialLinearNatural 3) := by
    rw [HasSectionModel,bot_subgroupOf]
    refine ⟨bot_le,hKA,le_normalizer_of_normal,inferInstance,
      QuotientGroup.quotientBot.trans a,?_⟩
    intro k x y hxy
    change r (b (inclusion hAZ y)).toAdd =
      specialLinearNatural 3 (linearThreeActor e k) (r (b (inclusion hAZ x)).toAdd)
    rw [hb k (inclusion hAZ x) (inclusion hAZ y) hxy,hre]
  let p : Z →* Multiplicative W := s.toMultiplicative.comp b.toMonoidHom
  have hps : Function.Surjective p := hs.comp b.surjective
  have hpk : p.ker=A.subgroupOf Z := by ext x; exact hk x
  let : (A.subgroupOf Z).Normal := hpk ▸ p.normal_ker
  let a : (Z ⧸ A.subgroupOf Z) ≃* Multiplicative W :=
    (QuotientGroup.quotientMulEquivOfEq hpk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective p hps)
  refine ⟨hbottom,hAZ,hKZ,hKA,inferInstance,a,?_⟩
  intro k x y hxy
  change s (b y).toAdd = specialLinearNatural 3 (linearThreeActor e k) (s (b x).toAdd)
  rw [hb k x y hxy,hse]

/-- A nonzero proper invariant subgroup of a doubled natural section is
natural, and its literal quotient in that section is natural at the same marking. -/
theorem proper_invariant_sections
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (hm : HasSectionModel K Z ⊥ (linearThreeActor e)
      ((specialLinearNatural (k := F) 3).prod (specialLinearNatural 3)))
    (hAZ : A ≤ Z) (hKA : K ≤ normalizer (A : Set G))
    (hne : A ≠ ⊥) (hlt : A ≠ Z) :
    HasSectionModel K A ⊥ (linearThreeActor e) (specialLinearNatural 3) ∧
      HasSectionModel K Z A (linearThreeActor e) (specialLinearNatural 3) := by
  rw [HasSectionModel,bot_subgroupOf] at hm
  obtain ⟨_,hKZ,_,hi,b0,hb0⟩ := hm
  let := hi
  let b : Z ≃* Multiplicative V := QuotientGroup.quotientBot.symm.trans b0
  have hb (k : K) (x y : Z) (hxy : (y:G)=k*(x:G)*(k:G)⁻¹) :
      (b y).toAdd=(specialLinearNatural 3 (linearThreeActor e k) (b x).toAdd.1,
        specialLinearNatural 3 (linearThreeActor e k) (b x).toAdd.2) := hb0 k x y hxy
  let D : AddSubgroup V := {
    carrier := {v | (b.symm (Multiplicative.ofAdd v) : G) ∈ A}
    zero_mem' := by change (b.symm 1 : G) ∈ A; rw [map_one]; exact A.one_mem
    add_mem' := by
      intro x y hx hy
      change (b.symm (Multiplicative.ofAdd x * Multiplicative.ofAdd y) : G) ∈ A
      rw [map_mul]
      exact A.mul_mem hx hy
    neg_mem' := by
      intro x hx
      change (b.symm (Multiplicative.ofAdd x)⁻¹ : G) ∈ A
      rw [map_inv]
      exact A.inv_mem hx }
  have hmem (x : Z) : (b x).toAdd ∈ D ↔ (x:G) ∈ A := by
    change (b.symm (b x) : G) ∈ A ↔ _
    rw [b.symm_apply_apply]
  have hDne : D ≠ ⊥ := by
    intro he
    apply hne
    apply bot_unique
    intro x hx
    have hh := (hmem ⟨x,hAZ hx⟩).mpr hx
    rw [he,AddSubgroup.mem_bot] at hh
    exact congrArg Z.subtype (b.map_eq_one_iff.mp (Multiplicative.toAdd.injective hh))
  have hDtop : D ≠ ⊤ := by
    intro he
    apply hlt
    apply le_antisymm hAZ
    intro x hx
    exact (hmem ⟨x,hx⟩).mp (he.symm ▸ AddSubgroup.mem_top _)
  have hDinv (g : SL(3,F)) (v : V) (hv : v ∈ D) :
      (specialLinearNatural 3 g v.1,specialLinearNatural 3 g v.2) ∈ D := by
    obtain ⟨k,hk⟩ := e.surjective.comp (QuotientGroup.mk'_surjective _) g
    let x : Z := b.symm (Multiplicative.ofAdd v)
    let y : Z := Z.normalizerMonoidHom ⟨k,hKZ k.property⟩ x
    have hy : (y:G) ∈ A := (mem_normalizer_iff.mp (hKA k.property) x).mp hv
    have hh := hb k x y rfl
    rw [show linearThreeActor e k=g from hk] at hh
    change (b y).toAdd=(specialLinearNatural 3 g (b (b.symm (Multiplicative.ofAdd v))).toAdd.1,
      specialLinearNatural 3 g (b (b.symm (Multiplicative.ofAdd v))).toAdd.2) at hh
    rw [b.apply_symm_apply] at hh
    exact hh ▸ (hmem y).mpr hy
  rcases SL3ParabolicNatural.invariant_double_natural_classification D hDne hDtop hDinv
    with hz | ⟨a,ha⟩
  · have hx (x : Z) : (x:G) ∈ A ↔ (b x).toAdd.1=0 := (hmem x).symm.trans (hz _)
    apply models_of_projection e hAZ hKZ hKA b hb (AddMonoidHom.snd W W) (AddMonoidHom.fst W W)
    · constructor
      · intro x y hxy
        apply Subtype.ext
        have he : inclusion hAZ x=inclusion hAZ y := b.injective
          (Multiplicative.toAdd.injective (Prod.ext
            ((hx _).mp x.property |>.trans ((hx _).mp y.property).symm) hxy))
        exact congrArg Z.subtype he
      · intro w
        let z : Z := b.symm (Multiplicative.ofAdd (0,w))
        have hzA : (z:G) ∈ A := (hx z).mpr (by dsimp [z]; rw [b.apply_symm_apply]; rfl)
        refine ⟨⟨z,hzA⟩,?_⟩
        change (b z).toAdd.2=w
        dsimp [z]
        rw [b.apply_symm_apply]
        rfl
    · intro w
      exact ⟨(w,0),rfl⟩
    · intro x
      exact (hx x).symm
    · intro g v; rfl
    · intro g v; rfl
  · have hx (x : Z) : (x:G) ∈ A ↔ (b x).toAdd.2=a • (b x).toAdd.1 :=
      (hmem x).symm.trans (ha _)
    let s : V →+ W := (AddMonoidHom.snd W W) -
      { toFun := fun v => a • v.1
        map_zero' := smul_zero a
        map_add' := fun v w => smul_add a v.1 w.1 }
    apply models_of_projection e hAZ hKZ hKA b hb (AddMonoidHom.fst W W) s
    · constructor
      · intro x y hxy
        apply Subtype.ext
        have he : inclusion hAZ x=inclusion hAZ y := b.injective
          (Multiplicative.toAdd.injective (Prod.ext hxy (by
            rw [(hx _).mp x.property,(hx _).mp y.property]
            exact congrArg (a • ·) hxy)))
        exact congrArg Z.subtype he
      · intro w
        let z : Z := b.symm (Multiplicative.ofAdd (w,a • w))
        have hzA : (z:G) ∈ A := (hx z).mpr (by dsimp [z]; rw [b.apply_symm_apply]; rfl)
        refine ⟨⟨z,hzA⟩,?_⟩
        change (b z).toAdd.1=w
        dsimp [z]
        rw [b.apply_symm_apply]
        rfl
    · intro w
      refine ⟨(0,w),?_⟩
      change w-a • (0:W)=w
      rw [smul_zero,sub_zero]
    · intro x
      exact sub_eq_zero.trans (hx x).symm
    · intro g v; rfl
    · intro g v
      change specialLinearNatural 3 g v.2-a • specialLinearNatural 3 g v.1=
        specialLinearNatural 3 g (v.2-a • v.1)
      rw [map_sub,map_smul]

private theorem exists_half_section
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (hm : HasSectionModel K Z ⊥ (linearThreeActor e)
      ((specialLinearNatural (k := F) 3).prod (specialLinearNatural 3))) :
    ∃ B : Subgroup G, B ≤ Z ∧
      HasSectionModel K B ⊥ (linearThreeActor e) (specialLinearNatural 3) ∧
      HasSectionModel K Z B (linearThreeActor e) (specialLinearNatural 3) := by
  have hm0 := hm
  rw [HasSectionModel,bot_subgroupOf] at hm
  obtain ⟨_,hKZ,_,hi,b0,hb0⟩ := hm
  let := hi
  let b : Z ≃* Multiplicative V := QuotientGroup.quotientBot.symm.trans b0
  let p : Z →* Multiplicative W := (AddMonoidHom.snd W W).toMultiplicative.comp b.toMonoidHom
  let B := p.ker.map Z.subtype
  have hBZ : B ≤ Z := map_subtype_le _
  have hB (x : Z) : (x:G) ∈ B ↔ (b x).toAdd.2=0 := by
    change (x:G) ∈ p.ker.map Z.subtype ↔ _
    exact mem_map_iff_mem Z.subtype_injective
  have hKB : K ≤ normalizer (B : Set G) := by
    apply le_normalizer_iff.mpr
    intro k hk x hx
    let xx : Z := ⟨x,hBZ hx⟩
    let y : Z := Z.normalizerMonoidHom ⟨k,hKZ hk⟩ xx
    apply (hB y).mpr
    have he := congrArg Prod.snd (hb0 ⟨k,hk⟩ xx y rfl)
    change (b y).toAdd.2=specialLinearNatural 3 (linearThreeActor e ⟨k,hk⟩) (b xx).toAdd.2 at he
    rw [he,(hB xx).mp hx,map_zero]
  have hBne : B ≠ ⊥ := by
    intro hz
    let x : Z := b.symm (Multiplicative.ofAdd ((fun _ : Fin 3 => (1:F)),0))
    have hx : (x:G) ∈ B := (hB x).mpr (by dsimp [x]; rw [b.apply_symm_apply]; rfl)
    have hx1 : x=1 := Subtype.ext (hz.le hx)
    have hh := congrArg (fun y : Multiplicative V => y.toAdd.1 0) (congrArg b hx1)
    dsimp [x] at hh
    rw [b.apply_symm_apply,map_one] at hh
    exact one_ne_zero hh
  have hBproper : B ≠ Z := by
    intro he
    let x : Z := b.symm (Multiplicative.ofAdd (0,(fun _ : Fin 3 => (1:F))))
    have hx : (x:G) ∈ B := he.symm ▸ x.property
    have hh := congrFun ((hB x).mp hx) 0
    dsimp [x] at hh
    rw [b.apply_symm_apply] at hh
    exact one_ne_zero hh
  exact ⟨B,hBZ,proper_invariant_sections e hm0 hBZ hKB hBne hBproper⟩

variable {Q : Subgroup G} [Finite G]
local notation "ZQ" => Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn Q

/-- Every nontrivial relative normal subgroup meets the doubled center in
that whole center or in a natural subgroup with natural quotient. The models
use the original full quotient marking and the literal intersection. -/
theorem normal_layer_sections
    (hQ : IsPGroup 2 Q)
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (hm : HasSectionModel K ZQ ⊥ (linearThreeActor e)
      ((specialLinearNatural (k := F) 3).prod (specialLinearNatural 3)))
    (hAQ : A ≤ Q) (hQA : Q ≤ normalizer (A : Set G))
    (hKA : K ≤ normalizer (A : Set G)) (hne : A ≠ ⊥) :
    ZQ ≤ A ∨
      (HasSectionModel K (ZQ ⊓ A) ⊥ (linearThreeActor e) (specialLinearNatural 3) ∧
        HasSectionModel K ZQ (ZQ ⊓ A) (linearThreeActor e) (specialLinearNatural 3)) := by
  by_cases hZA : ZQ ≤ A
  · exact Or.inl hZA
  right
  apply proper_invariant_sections e hm inf_le_left
    ((le_inf hm.2.1 hKA).trans inf_normalizer_le_normalizer_inf)
  · intro hz
    have hi := inf_omegaCenterIn_ne_bot_of_normalized_twoGroup A Q hAQ hQ hQA hne
    apply hi
    apply bot_unique
    exact (le_inf (inf_le_right.trans (map_mono (map_subtype_le _))) inf_le_left).trans_eq hz
  · intro he
    exact hZA (he.symm ▸ (inf_le_right : ZQ ⊓ A ≤ A))

/-- In the nonabelian doubled-center branch, the actual derived and
Frattini layers both have the preceding marked central flags. Their
intersections are nontrivial and retain the literal containment Q' ≤ Φ(Q). -/
theorem derived_frattini_sections
    (hQ : IsPGroup 2 Q) (hKQ : K ≤ normalizer (Q : Set G))
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (hm : HasSectionModel K ZQ ⊥ (linearThreeActor e)
      ((specialLinearNatural (k := F) 3).prod (specialLinearNatural 3)))
    (hna : ¬ IsMulCommutative Q) :
    ZQ ⊓ ⁅Q,Q⁆ ≠ ⊥ ∧ ZQ ⊓ ⁅Q,Q⁆ ≤ ZQ ⊓ frattiniIn Q ∧
      (ZQ ≤ ⁅Q,Q⁆ ∨
        (HasSectionModel K (ZQ ⊓ ⁅Q,Q⁆) ⊥ (linearThreeActor e) (specialLinearNatural 3) ∧
          HasSectionModel K ZQ (ZQ ⊓ ⁅Q,Q⁆) (linearThreeActor e) (specialLinearNatural 3))) ∧
      (ZQ ≤ frattiniIn Q ∨
        (HasSectionModel K (ZQ ⊓ frattiniIn Q) ⊥ (linearThreeActor e) (specialLinearNatural 3) ∧
          HasSectionModel K ZQ (ZQ ⊓ frattiniIn Q) (linearThreeActor e) (specialLinearNatural 3))) := by
  have hD : (⁅Q,Q⁆ : Subgroup G) ≠ ⊥ := by
    intro hd
    rw [←map_subtype_commutator] at hd
    exact hna ((_root_.commutator_eq_bot_iff Q).mp
      ((map_eq_bot_iff_of_injective _ Q.subtype_injective).mp hd))
  have hKD : K ≤ normalizer ((⁅Q,Q⁆ : Subgroup G) : Set G) := by
    rw [←map_subtype_commutator]
    exact hKQ.trans (normalizer_le_normalizer_characteristic_image Q (_root_.commutator Q))
  have hQD := normalizer_commutator_ge_left Q Q
  have hi : ZQ ⊓ ⁅Q,Q⁆ ≠ ⊥ := by
    intro hz
    apply inf_omegaCenterIn_ne_bot_of_normalized_twoGroup ⁅Q,Q⁆ Q Q.commutator_le_self hQ hQD hD
    exact bot_unique ((le_inf (inf_le_right.trans (map_mono (map_subtype_le _))) inf_le_left).trans_eq hz)
  let : Fact (IsPGroup 2 Q) := ⟨hQ⟩
  have hDP : (⁅Q,Q⁆ : Subgroup G) ≤ frattiniIn Q := by
    rw [←map_subtype_commutator]
    exact map_mono (commutator_le_frattini_of_isPGroup (p := 2))
  have hQP : Q ≤ normalizer (frattiniIn Q : Set G) := Q.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image Q (frattini Q))
  have hKP : K ≤ normalizer (frattiniIn Q : Set G) := hKQ.trans
    (normalizer_le_normalizer_characteristic_image Q (frattini Q))
  exact ⟨hi,inf_le_inf_left _ hDP,
    normal_layer_sections hQ e hm Q.commutator_le_self hQD hKD hD,
    normal_layer_sections hQ e hm (map_subtype_le _) hQP hKP
      (fun he => hD (bot_unique (hDP.trans_eq he)))⟩

/-- A nonabelian two-group with doubled natural center has an actual
natural central subgroup in Q' and Φ(Q), with natural quotient in the
whole center, all at the supplied quotient marking. -/
theorem exists_derived_central_flag
    (hQ : IsPGroup 2 Q) (hKQ : K ≤ normalizer (Q : Set G))
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (hm : HasSectionModel K ZQ ⊥ (linearThreeActor e)
      ((specialLinearNatural (k := F) 3).prod (specialLinearNatural 3)))
    (hna : ¬ IsMulCommutative Q) :
    ∃ B : Subgroup G, B ≤ ZQ ∧ B ≤ ⁅Q,Q⁆ ∧ B ≤ frattiniIn Q ∧
      HasSectionModel K B ⊥ (linearThreeActor e) (specialLinearNatural 3) ∧
      HasSectionModel K ZQ B (linearThreeActor e) (specialLinearNatural 3) := by
  have hh := derived_frattini_sections hQ hKQ e hm hna
  let : Fact (IsPGroup 2 Q) := ⟨hQ⟩
  have hDP : (⁅Q,Q⁆ : Subgroup G) ≤ frattiniIn Q := by
    rw [←map_subtype_commutator]
    exact map_mono (commutator_le_frattini_of_isPGroup (p := 2))
  rcases hh.2.2.1 with hZD | hs
  · obtain ⟨B,hBZ,hB,hquot⟩ := exists_half_section e hm
    exact ⟨B,hBZ,hBZ.trans hZD,hBZ.trans (hZD.trans hDP),hB,hquot⟩
  · exact ⟨ZQ ⊓ ⁅Q,Q⁆,inf_le_left,inf_le_right,inf_le_right.trans hDP,hs⟩

variable {R : Subgroup G} {n : ℕ} [Finite F] [CharP F 2]
variable (h : LinearThreeMSPair KnownSimple.IsKnownSimple K R n F) (hn : 1 < n)
include h hn

/-- The genuine doubled-omega MS branch supplies marked flags on both
actual characteristic layers, in every nonbinary degree. The center is
reconstructed at the supplied marking before taking either intersection. -/
theorem ms_derived_frattini_sections
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (hm : HasSectionModel K
      (Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.omegaCenterIn (msQ K R))
      ⊥ (linearThreeActor e)
      ((specialLinearNatural (k := F) 3).prod (specialLinearNatural 3)))
    (hna : ¬ IsMulCommutative (msQ K R)) :
    let Q := msQ K R
    let Z := Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn Q
    Z ⊓ ⁅Q,Q⁆ ≠ ⊥ ∧ Z ⊓ ⁅Q,Q⁆ ≤ Z ⊓ frattiniIn Q ∧
      (Z ≤ ⁅Q,Q⁆ ∨
        (HasSectionModel K (Z ⊓ ⁅Q,Q⁆) ⊥ (linearThreeActor e) (specialLinearNatural 3) ∧
          HasSectionModel K Z (Z ⊓ ⁅Q,Q⁆) (linearThreeActor e) (specialLinearNatural 3))) ∧
      (Z ≤ frattiniIn Q ∨
        (HasSectionModel K (Z ⊓ frattiniIn Q) ⊥ (linearThreeActor e) (specialLinearNatural 3) ∧
          HasSectionModel K Z (Z ⊓ frattiniIn Q) (linearThreeActor e) (specialLinearNatural 3))) :=
  derived_frattini_sections
    ((isPGroup_pCoreIn 2 (K ⊔ R)).to_le msQ_le_joinCore)
    ((le_sup_left : K ≤ K ⊔ R).trans (CentralSections.join_normalizes_core h hn))
    e (DoubledCenter.center_doubled h hn e hm) hna

end CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.CentralDerivedSections
