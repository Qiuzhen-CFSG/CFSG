module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.SylowNormalizer.JankoTerminal.SL3Cartan
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.SylowNormalizer.JankoTerminal.Fixer
public import Theory.SpecificGroups.PSL3.LinearThreeCubicCartan

/-!
# Excluding the actual SL₃(4) J₁ configuration

The literal odd section centralizer has exponent three and acts trivially
on the local PSL₂ section. The full SL₃(4) calculation makes its image scalar,
so Q = [X,T] lies in O₂(LT). Coprime commutator idempotence identifies Q with
[X,O₂(LT)]; expressing this subgroup as a residual intersection shows that
L normalizes it. The already proved J₁ fixer theorem gives K-normality.
The nontriviality proved in SL3Cartan and the actual intersection escape
then yield the common-normalizer contradiction.

The line-action consumer in LineAction/SL3 applies this contradiction to
the full source catalogue and proves both 11.2.3 conclusions, retaining only
the radical alternative owned by qt-d-1222-natural-normalizer-source.
The Sp₄(4) and G₂(4) terminal branches remain with this task's assembly.

Source: Aschbacher--Smith 3.3.16, printed p.591.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation Matrix Matrix.PSL3
open scoped MatrixGroups commutatorElement Pointwise
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
-- Odd order identifies the commutator as an invariant residual intersection.
private theorem normalize_displacement {G : Type*} [Group G] [Finite G]
    (R X K : Subgroup G) (hR : IsPGroup 2 R)
    (hodd : Odd (Nat.card X))
    (hXR : X ≤ normalizer (R : Set G))
    (hKR : K ≤ normalizer (R : Set G))
    (hKX : ⁅X,K⁆ ≤ R) : K ≤ normalizer ((⁅X,R⁆ : Subgroup G) : Set G) := by
  have hX : IsPPerfect 2 X := by
    apply (pResidual_eq_top_iff 2 X).mp
    apply top_unique
    intro x _
    exact mem_pResidual_of_orderOf_coprime
      ((Nat.coprime_two_left.mpr hodd).of_dvd_right (orderOf_dvd_natCard x))
  let J := R ⊔ X
  let Z := (pResidual 2 J).map J.subtype
  have hZ : Z = X ⊔ ⁅R,X⁆ := embedded_pResidual_sup_eq_sup_commutator R X hR hX
  have hRZ : R ⊓ Z = ⁅R,X⁆ := by
    have hc : ⁅R,X⁆ ≤ R := le_normalizer_iff_commutator_le_left.mp hXR
    have hd : Disjoint X R := by
      apply disjoint_of_coprime_natCard
      obtain ⟨n,hn⟩ := hR.exists_card_eq
      rw [hn]
      exact (Nat.coprime_two_right.mpr hodd).pow_right n
    apply le_antisymm
    · rintro r ⟨hr,hz⟩
      rw [hZ] at hz
      change r ∈ ((X ⊔ ⁅R,X⁆ : Subgroup G) : Set G) at hz
      rw [coe_mul_of_left_le_normalizer_right _ _ (normalizer_commutator_ge_right R X)] at hz
      obtain ⟨x,hx,d,hd',hxd⟩ := hz
      have hxR : x ∈ R := by
        have hh := R.mul_mem hr (R.inv_mem (hc hd'))
        rw [← hxd,mul_inv_cancel_right] at hh
        exact hh
      have hx1 : x = 1 := mem_bot.mp (hd.eq_bot ▸ (show x ∈ X ⊓ R from ⟨hx,hxR⟩))
      have he : d = r := by simpa only [hx1,one_mul] using hxd
      exact he ▸ hd'
    · rw [hZ]
      exact le_inf hc le_sup_right
  have hn : K ≤ normalizer (J : Set G) := by
    apply le_normalizer_iff.mpr
    intro k hk g hg
    have hh : J ≤ J.comap (MulAut.conj k).toMonoidHom := by
      apply sup_le
      · intro r hr
        exact mem_sup_left ((mem_normalizer_iff.mp (hKR hk) _).mp hr)
      · intro x hx
        have hcomm : ⁅k,x⁆ ∈ R := by
          rw [commutator_comm] at hKX
          exact hKX (commutator_mem_commutator hk hx)
        have hh := J.mul_mem (mem_sup_left hcomm) (mem_sup_right hx)
        change k * x * k⁻¹ ∈ J
        simpa only [MulAut.conj_apply,commutatorElement_def,mul_assoc,inv_mul_cancel,mul_one] using hh
    exact hh hg
  have hKZ : K ≤ normalizer (Z : Set G) :=
    hn.trans (normalizer_le_normalizer_characteristic_image J (pResidual 2 J))
  rw [commutator_comm X R,←hRZ]
  exact (le_inf hKR hKZ).trans inf_normalizer_le_normalizer_inf

private theorem coprime_displacement_eq {G : Type*} [Group G] [Finite G]
    (R X T : Subgroup G) (hT : IsPGroup 2 T) (hodd : Odd (Nat.card X))
    (hXT : X ≤ normalizer (T : Set G))
    (hRT : R ≤ T) (hQ : ⁅X,T⁆ ≤ R) : ⁅X,T⁆ = ⁅X,R⁆ := by
  have hc : ∀ x ∈ (X : Set G), Nat.Coprime (orderOf x) (Nat.card T) := by
    intro x hx
    obtain ⟨n,hn⟩ := hT.exists_card_eq
    rw [hn]
    have hd : orderOf x ∣ Nat.card X := by
      change orderOf ((⟨x,hx⟩ : X) : G) ∣ Nat.card X
      rw [Subgroup.orderOf_coe]
      exact orderOf_dvd_natCard _
    exact ((Nat.coprime_two_right.mpr hodd).of_dvd_left hd).pow_right n
  have he := commutator_closure_coprime_idempotent T (X : Set G)
    (by simpa only [closure_eq] using hXT) hc
  simp only [closure_eq] at he
  apply le_antisymm
  · rw [commutator_comm X T,←he]
    rw [commutator_comm X T] at hQ
    exact (commutator_mono hQ le_rfl).trans_eq (commutator_comm R X)
  · exact commutator_mono le_rfl hRT

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer.SL3Terminal
open PointCohomology.PointGeometry.SL3Core
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
  (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
  (a : SL(3, S.field.Carrier))

private theorem section_commutator_le {f : InvariantFlag (Coordinates.sl3 m)}
    {A : OddSupplement T} (E : JankoConfiguration S f A) :
    ⁅E.oddSectionCentralizer,f.Li E.index⁆ ≤ (f.Li E.index).pCoreIn 2 := by
  rw [commutator_le]
  intro x hx y hy
  obtain ⟨a,ha,hax⟩ := hx.2
  change (a : G) = x at hax
  let y' : f.Li E.index := ⟨y,hy⟩
  let z := (f.Li E.index).normalizerMonoidHom a y' * y'⁻¹
  have hz : z ∈ pCore 2 (f.Li E.index) := by
    apply (QuotientGroup.eq_one_iff z).mp
    have hh := DFunLike.congr_fun (show coreQuotientAction (f.Li E.index) a = 1 from ha)
      (QuotientGroup.mk' (pCore 2 (f.Li E.index)) y')
    simp only [coreQuotientAction,MonoidHom.comp_apply,quotientAut_apply_mk,MulAut.one_apply] at hh
    change QuotientGroup.mk' (pCore 2 (f.Li E.index))
      ((f.Li E.index).normalizerMonoidHom a y' * y'⁻¹) = 1
    rw [map_mul,map_inv,hh,mul_inv_cancel]
  have hm := mem_map_of_mem (f.Li E.index).subtype hz
  change (a : G) * y * (a : G)⁻¹ * y⁻¹ ∈ (f.Li E.index).pCoreIn 2 at hm
  simpa only [hax,commutatorElement_def] using hm

/-- The literal odd section centralizer has scalar image in the full SL₃(4) quotient. -/
theorem section_image_central
    {A : OddSupplement T} (E : JankoConfiguration S (SL3.flag D S m) A)
    (x : E.oddSectionCentralizer) :
    SL3.PlaneAction.alignedQuotient D S m ⟨x,x.property.1.2⟩ ∈
      center SL(3,S.field.Carrier) := by
  let f := SL3.flag D S m
  let q := SL3.PlaneAction.alignedQuotient D S m
  let X := E.oddSectionCentralizer
  let Y := f.Li E.index
  have hXL : X ≤ L := inf_le_left.trans inf_le_right
  have hYL : Y ≤ L := (localResidual_le _).trans inf_le_left
  have hc : ⁅X.subgroupOf L,Y.subgroupOf L⁆ ≤ (Y.pCoreIn 2).subgroupOf L := by
    apply (map_le_map_iff_of_injective L.subtype_injective).mp
    rw [map_commutator,map_subgroupOf_eq_of_le hXL,map_subgroupOf_eq_of_le hYL,
      map_subgroupOf_eq_of_le ((pCoreIn_le 2 Y).trans hYL)]
    exact section_commutator_le D S m E
  have hk : IsPGroup 2 q.ker := by
    rw [SL3.PlaneAction.alignedQuotient_ker]
    exact pCore_isPGroup
  have hm := map_mono (f := q) hc
  rw [map_commutator,←pCoreIn_subgroupOf 2 Y L hYL,
    map_pCoreIn_of_ker_isPGroup q hk,SL3.PlaneAction.local_image] at hm
  let z := q ⟨x,x.property.1.2⟩
  have hz : z ^ 3 = 1 := by
    have hh := congrArg (fun y : (A.subgroup ⊓ L : Subgroup G) => (y : G))
      (intersection_cube D S m E ⟨x,x.property.1⟩)
    have hh' : (⟨x,x.property.1.2⟩ : L)^3 = 1 := Subtype.ext hh
    exact (map_pow q _ 3).symm.trans ((congrArg q hh').trans q.map_one)
  have hzX : z ∈ (X.subgroupOf L).map q := ⟨⟨x,x.property.1.2⟩,x.property,rfl⟩
  have hcomm := (commutator_mono (zpowers_le.mpr hzX) le_rfl).trans hm
  have hF : Nat.card S.field.Carrier = 4 := by rw [S.field.card_eq,E.degree_eq_two]; rfl
  by_cases hi : E.index = 0
  · apply Matrix.PSL3.LinearThree.cubic_point_section_central hF z _ hz
    simpa only [hi,SL3.PlaneAction.localGroup,Matrix.cons_val_zero] using hcomm
  · have hi' : E.index = 1 := by omega
    apply Matrix.PSL3.LinearThree.cubic_line_section_central hF z _ hz
    simpa only [hi',SL3.PlaneAction.localGroup,Matrix.cons_val_one,Matrix.cons_val_zero] using hcomm

/-- Scalarity puts the actual odd section centralizer in the projective-action kernel. -/
theorem section_le_projective_kernel {A : OddSupplement T}
    (E : JankoConfiguration S (SL3.flag D S m) A) :
    E.oddSectionCentralizer ≤ ((projectiveAction D S m (SL3.alignment D S m)⁻¹).ker.map
      (L ⊔ (T : Subgroup G)).subtype) := by
  intro x hx
  let l : L := ⟨x,hx.1.2⟩
  refine ⟨inclusion le_sup_left l,?_,rfl⟩
  change projectiveAction D S m (SL3.alignment D S m)⁻¹ (inclusion le_sup_left l) = 1
  rw [projectiveAction_component]
  change MulAut.conj (QuotientGroup.mk' (center SL(3,S.field.Carrier))
    (SL3.PlaneAction.alignedQuotient D S m l)) = 1
  have hh : QuotientGroup.mk' (center SL(3,S.field.Carrier))
      (SL3.PlaneAction.alignedQuotient D S m l) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (section_image_central D S m E ⟨x,hx⟩)
  rw [hh,map_one]

/-- The source displacement is normal in L in the full linear-three branch. -/
theorem displacement_normalized_by_L {A : OddSupplement T}
    (E : JankoConfiguration S (SL3.flag D S m) A) :
    L ≤ normalizer (E.displacement : Set G) := by
  let H := L ⊔ (T : Subgroup G)
  let R := H.pCoreIn 2
  let X := E.oddSectionCentralizer
  let b := projectiveAction D S m (SL3.alignment D S m)⁻¹
  let Z := b.ker.map H.subtype
  have hnZ : H ≤ normalizer (Z : Set G) := by
    intro g hg
    exact b.ker.le_normalizer_map H.subtype
      ⟨⟨g,hg⟩,b.ker.normalizer_eq_top ▸ mem_top _,rfl⟩
  have hQZ : E.displacement ≤ Z :=
    (commutator_mono (section_le_projective_kernel D S m E) le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp (le_sup_right.trans hnZ))
  have hQR : E.displacement ≤ R :=
    (le_inf E.displacement_le_sylow hQZ).trans
      (sylow_inf_projective_kernel_le_core D S m (SL3.alignment D S m)⁻¹)
  have hnR : H ≤ normalizer (R : Set G) :=
    H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hXL : X ≤ L := inf_le_left.trans inf_le_right
  have hRX : X ≤ normalizer (R : Set G) := hXL.trans (le_sup_left.trans hnR)
  have hRL : L ≤ normalizer (R : Set G) := le_sup_left.trans hnR
  have hXR : ⁅X,L⁆ ≤ R := by
    rw [commutator_le]
    intro x hx l hl
    obtain ⟨z,hz,hzx⟩ := section_le_projective_kernel D S m E hx
    have hh := projectiveAction_kernel_commutator D S m (SL3.alignment D S m)⁻¹ z hz ⟨l,hl⟩
    change (z : G) = x at hzx
    rw [hzx] at hh
    exact pCoreIn_mono_of_normalizes le_sup_left
      (sup_le L.le_normalizer D.sylow_normalizes_component) hh
  have hRT : R ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le
      (show (T : Subgroup G) ≤ H from le_sup_right)] using pCoreIn_le_sylow H (T.subtype le_sup_right)
  have hodd : Odd (Nat.card X) := A.odd.of_dvd_nat (card_dvd_of_le (inf_le_left.trans inf_le_left))
  have hXT : X ≤ normalizer (T : Set G) := (inf_le_left.trans inf_le_left).trans A.normalizes
  have he : E.displacement = ⁅X,R⁆ :=
    coprime_displacement_eq R X T T.isPGroup' hodd hXT hRT hQR
  rw [he]
  exact normalize_displacement R X L (pCore_isPGroup.map _) hodd hRX hRL hXR

/-- The complete field-four linear-three terminal contradiction on the literal configuration. -/
theorem false_of_sl3 {A : OddSupplement T}
    (E : JankoConfiguration S (SL3.flag D S m) A) : False :=
  E.false_of_displacement_normalized_by_L (section_ne_bot D S m E)
    (displacement_normalized_by_L D S m E)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer.SL3Terminal
