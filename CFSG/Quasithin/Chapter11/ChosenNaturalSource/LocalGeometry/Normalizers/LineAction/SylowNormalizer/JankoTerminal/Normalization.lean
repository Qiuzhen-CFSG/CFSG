module
public import Theory.GroupTheory.PResidual.SupplementCommutator
public import Theory.GroupTheory.PResidualCommutator
public import Theory.GroupTheory.PResidual.NormalizerCore
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.SylowNormalizer.JankoTerminal.SectionImage

/-!
# Normality of the source displacement in the J₁ component

Let X be the literal odd section centralizer and Q = [X,T]. If X acts
trivially on K/O₂(K), then Q lies in R = O₂(KT). Coprime commutator
idempotence gives Q = [X,R]. The latter subgroup equals the intersection
of R with O²(RX); K normalizes both factors, hence normalizes Q.

The actual action of X fixes the residual image pointwise, by SectionImage.
If its pointwise fixer in Aut(K/O₂(K)) is a two-group, odd order kills the
X-action. The final applications discharge K-normality in both the
common-normal and order-nineteen terminal contradictions.

The pointwise-fixer model bound, nontrivial cubic X, SL₃ normality and
Sp₄ size/movement inputs remain explicit. Their discharge, the G₂ exclusion
and construction of the J₁ configuration remain with the assembly owner
qt-d-1222-natural-line-action; these conditional applications do not claim
source 3.3.16 or Sylow-normalizer containment.

Source: Aschbacher--Smith, 3.3.16, printed p.591.
-/

@[expose] public noncomputable section
open Subgroup
open scoped commutatorElement

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

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer
variable {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {c : Coordinates D S.field} {f : InvariantFlag c}
    {A : OddSupplement T} (E : JankoConfiguration S f A)
namespace JankoConfiguration

/-- The kernel of the original action on the component quotient, in G. -/
def componentSectionCentralizer : Subgroup G :=
  (coreQuotientAction E.component).ker.map (normalizer (E.component : Set G)).subtype

/-- Relative normality in the enlarged parabolic includes normalization by T. -/
theorem sylow_normalizes_component :
    (T : Subgroup G) ≤ normalizer (E.component : Set G) :=
  (le_sup_right.trans le_sup_left).trans
    ((normal_subgroupOf_iff_le_normalizer E.normal_component.1.1).mp E.normal_component.2)

private theorem component_quotient_center :
    center (E.component ⧸ pCore 2 E.component) = ⊥ := by
  let H := (f.Li E.index ⊔ (T : Subgroup G)) ⊔ A.subgroup
  let : Group.IsPerfect (E.component.subgroupOf H) := E.normal_component.1.2.perfect
  let d := subgroupOfEquivOfLe E.normal_component.1.1
  let : Group.IsPerfect E.component := Group.IsPerfect.ofSurjective (f := d.toMonoidHom) d.surjective
  obtain ⟨e⟩ := E.model
  let : IsSimpleGroup (E.component ⧸ pCore 2 E.component) := e.isSimpleGroup
  rcases (inferInstance : (center (E.component ⧸ pCore 2 E.component)).Normal).eq_bot_or_eq_top with hb | ht
  · exact hb
  · exact (Group.IsPerfect.not_isMulCommutative (E.component ⧸ pCore 2 E.component)
      (center_eq_top_iff.mp ht)).elim

/-- Section centralization bounds commutators with K by the embedded O₂(K). -/
theorem componentSectionCentralizer_commutator_le :
    ⁅E.componentSectionCentralizer,E.component⁆ ≤ E.component.pCoreIn 2 := by
  rw [commutator_le]
  intro x hx k hk
  obtain ⟨a,ha,hax⟩ := hx
  change (a : G) = x at hax
  let k' : E.component := ⟨k,hk⟩
  let z := E.component.normalizerMonoidHom a k' * k'⁻¹
  have hz : z ∈ pCore 2 E.component := by
    apply (QuotientGroup.eq_one_iff z).mp
    have hh := DFunLike.congr_fun (show coreQuotientAction E.component a = 1 from ha)
      (QuotientGroup.mk' (pCore 2 E.component) k')
    simp only [coreQuotientAction,MonoidHom.comp_apply,quotientAut_apply_mk,MulAut.one_apply] at hh
    change QuotientGroup.mk' (pCore 2 E.component)
      (E.component.normalizerMonoidHom a k' * k'⁻¹) = 1
    rw [map_mul,map_inv,hh,mul_inv_cancel]
  have hm := mem_map_of_mem E.component.subtype hz
  change (a : G) * k * (a : G)⁻¹ * k⁻¹ ∈ E.component.pCoreIn 2 at hm
  simpa only [hax,commutatorElement_def] using hm

/-- Trivial quotient action puts the original displacement inside O₂(KT). -/
theorem displacement_le_component_radical
    (hX : E.oddSectionCentralizer ≤ E.componentSectionCentralizer) :
    E.displacement ≤ (E.component ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let K := E.component
  let J := K ⊔ (T : Subgroup G)
  have hn : J ≤ normalizer (K : Set G) := sup_le K.le_normalizer E.sylow_normalizes_component
  let a := (coreQuotientAction K).comp (inclusion hn)
  have he : a = pCoreJoinAction 2 E.sylow_normalizes_component := by
    ext g u
    induction u using Quotient.inductionOn with | h u => rfl
  have hk : a.ker = pCore 2 J := by
    rw [he]
    exact pCoreJoinAction_kernel 2 E.sylow_normalizes_component T.isPGroup' E.component_quotient_center
  have hnorm : normalizer (K : Set G) ≤ normalizer (E.componentSectionCentralizer : Set G) := by
    intro g hg
    exact (coreQuotientAction K).ker.le_normalizer_map (normalizer (K : Set G)).subtype
      ⟨⟨g,hg⟩,(coreQuotientAction K).ker.normalizer_eq_top ▸ mem_top _,rfl⟩
  have hQ : E.displacement ≤ E.componentSectionCentralizer :=
    (commutator_mono hX le_rfl).trans (le_normalizer_iff_commutator_le_left.mp
      (E.sylow_normalizes_component.trans hnorm))
  intro g hg
  have hgJ : g ∈ J := mem_sup_right (E.displacement_le_sylow hg)
  have hga : (⟨g,hgJ⟩ : J) ∈ a.ker := by
    obtain ⟨b,hb,hbg⟩ := hQ hg
    have hb' : b = inclusion hn ⟨g,hgJ⟩ := Subtype.ext hbg
    change inclusion hn ⟨g,hgJ⟩ ∈ (coreQuotientAction K).ker
    exact hb' ▸ hb
  exact mem_map_of_mem J.subtype (hk ▸ hga)

/-- K normalizes the original Q once X centralizes its quotient. -/
theorem component_normalizes_displacement
    (hX : E.oddSectionCentralizer ≤ E.componentSectionCentralizer) :
    E.component ≤ normalizer (E.displacement : Set G) := by
  let R := (E.component ⊔ (T : Subgroup G)).pCoreIn 2
  have hodd : Odd (Nat.card E.oddSectionCentralizer) :=
    A.odd.of_dvd_nat (card_dvd_of_le (inf_le_left.trans inf_le_left : E.oddSectionCentralizer ≤ A.subgroup))
  have hRT : R ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ E.component ⊔ T from le_sup_right)] using
      pCoreIn_le_sylow (E.component ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  have hnR : E.component ⊔ (T : Subgroup G) ≤ normalizer (R : Set G) :=
    (E.component ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 (E.component ⊔ (T : Subgroup G) : Subgroup G)))
  have hXR : E.oddSectionCentralizer ≤ normalizer (R : Set G) := by
    have hxK : E.oddSectionCentralizer ≤ normalizer (E.component : Set G) :=
      hX.trans (map_subtype_le _)
    exact ((le_inf hxK ((inf_le_left.trans inf_le_left : E.oddSectionCentralizer ≤ A.subgroup).trans A.normalizes)).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)).trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 (E.component ⊔ (T : Subgroup G) : Subgroup G)))
  have hKX : ⁅E.oddSectionCentralizer,E.component⁆ ≤ R :=
    ((commutator_mono hX le_rfl).trans E.componentSectionCentralizer_commutator_le).trans
      (pCoreIn_mono_of_normalizes le_sup_left (sup_le E.component.le_normalizer E.sylow_normalizes_component))
  have he : E.displacement = ⁅E.oddSectionCentralizer,R⁆ :=
    coprime_displacement_eq R E.oddSectionCentralizer T T.isPGroup' hodd
      ((inf_le_left.trans inf_le_left : E.oddSectionCentralizer ≤ A.subgroup).trans A.normalizes)
      hRT (E.displacement_le_component_radical hX)
  rw [he]
  exact normalize_displacement R E.oddSectionCentralizer E.component
    (pCore_isPGroup.map _) hodd hXR (le_sup_left.trans hnR) hKX

/-- The actual pointwise fixer in the automorphism group of K/O₂(K). -/
def residualImageFixer : Subgroup (MulAut (E.component ⧸ pCore 2 E.component)) :=
  fixingSubgroup (MulAut (E.component ⧸ pCore 2 E.component))
    (E.residualImage : Set (E.component ⧸ pCore 2 E.component))

/-- The source pointwise-fixer model bound kills the odd X-action on K/O₂(K). -/
theorem oddSectionCentralizer_le_componentSectionCentralizer
    (hfixer : IsPGroup 2 E.residualImageFixer) :
    E.oddSectionCentralizer ≤ E.componentSectionCentralizer := by
  have hxN : E.oddSectionCentralizer ≤ normalizer (E.component : Set G) :=
    (inf_le_left.trans inf_le_left : E.oddSectionCentralizer ≤ A.subgroup).trans
      (le_sup_right.trans ((normal_subgroupOf_iff_le_normalizer E.normal_component.1.1).mp
        E.normal_component.2))
  let a := (coreQuotientAction E.component).comp (inclusion hxN)
  have hodd : Odd (Nat.card E.oddSectionCentralizer) :=
    A.odd.of_dvd_nat (card_dvd_of_le (inf_le_left.trans inf_le_left : E.oddSectionCentralizer ≤ A.subgroup))
  obtain ⟨n,hn⟩ := hfixer.exists_card_eq
  intro x hx
  let x' : E.oddSectionCentralizer := ⟨x,hx⟩
  have ha : a x' ∈ E.residualImageFixer := by
    intro y
    exact E.oddSectionCentralizer_fixes_residualImage x' y
  have ho : orderOf (a x') ∣ 2 ^ n := by
    rw [←hn]
    change orderOf ((⟨a x',ha⟩ : E.residualImageFixer) : MulAut (E.component ⧸ pCore 2 E.component)) ∣ Nat.card E.residualImageFixer
    rw [Subgroup.orderOf_coe]
    exact orderOf_dvd_natCard _
  have ho' : orderOf (a x') ∣ Nat.card E.oddSectionCentralizer :=
    (orderOf_map_dvd a x').trans (orderOf_dvd_natCard x')
  have hone : a x' = 1 := orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes ((Nat.coprime_two_right.mpr hodd).pow_right n) ho' ho)
  exact ⟨inclusion hxN x',hone,rfl⟩

/-- The full source component normalizes Q from the literal pointwise-fixer bound. -/
theorem component_normalizes_displacement_of_fixer
    (hfixer : IsPGroup 2 E.residualImageFixer) :
    E.component ≤ normalizer (E.displacement : Set G) :=
  E.component_normalizes_displacement (E.oddSectionCentralizer_le_componentSectionCentralizer hfixer)

/-- The common-normal terminal contradiction with its K-normality proved. -/
theorem false_of_common_normal_of_fixer
    (hfixer : IsPGroup 2 E.residualImageFixer)
    (hne : E.oddSectionCentralizer ≠ ⊥)
    (hLQ : L ≤ normalizer (E.displacement : Set G)) : False :=
  E.false_of_displacement_common_normal hne hLQ (E.component_normalizes_displacement_of_fixer hfixer)

/-- The order-nineteen terminal contradiction with its K-normality proved. -/
theorem false_of_small_displacement_of_fixer
    (hfixer : IsPGroup 2 E.residualImageFixer)
    (hsmall : Nat.card E.displacement ≤ 2 ^ 16)
    (hmoves : ¬ f.Li E.index ≤ centralizer (E.displacement : Set G)) : False :=
  E.false_of_displacement_small hsmall (E.component_normalizes_displacement_of_fixer hfixer) hmoves

end JankoConfiguration
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer
