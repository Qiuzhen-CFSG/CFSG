module
public import CFSG.Quasithin.Chapter13.Section05.AmbientSource.Displacement
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.Residual
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix.Basic
public import Theory.GroupTheory.Commutator.PerfectCoreKernel

/-!
# The source normalizer paragraph of 13.3.14(b)

For the original natural A₆ configuration, a two-perfect subgroup of
M centralizing V₃ acts trivially on V: the TI theorem places it in M_V,
and its action has elementary two-group image by the exact displacement
bound. The action kernel on L is the full central-core preimage, including
the central three-cover. Perfectness removes this central image modulo
O₂(L), recovering normalization of the two-perfect subgroup.

The subgroup is normal only in its product with the original Sylow.
The source point puts that product in characteristic two. Its nontrivial
core and the genuine unique-maximal-local theorem then bound the whole
normalizer by M. The actual residual Y=O²(C_G(<V₃^{G₁}>)) consequently
cannot be contained in M unless it is trivial.

The remaining earlier inputs are perfectness from 13.3.2, TI from 12.2.6,
unique maximal-local containment from 13.3.2/1.2.7, and escape from 13.3.6.
The cubic-intersection, odd-rank and solvability conclusions of reduction
(b), and all later reductions of 13.3.14, are not asserted here.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.3.14(b), first paragraph, printed p.891.
-/

@[expose] public noncomputable section
open Subgroup
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section03.Noncentrality
open Section08.SourceCompletion Section05.AmbientSource
open Section08.TransvectionRecognition.Component.ModelExtension
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V P E U M H : Subgroup G}
  (d : NaturalSetup T L V P E U M H)

include d
/-- The original natural action has its genuine central-cover kernel. -/
theorem natural_action_kernel :
    L ⊓ centralizer (V : Set G) = (centralCore L).map L.subtype := by
  apply le_antisymm
  · intro l hl
    let lL : L := ⟨l,hl.1⟩
    have hq : QuotientGroup.mk' (centralCore L) lL = 1 := by
      apply d.local_quotient.injective
      rw [map_one]
      apply Section08.ComponentSieve.SixAndG2.NaturalSix.alternatingAction_injective
      apply LinearMap.ext
      intro w
      obtain ⟨v,hv⟩ := d.coordinate.surjective (Multiplicative.ofAdd w)
      have he := d.conjugation lL v
      have hc : V.normalizerMonoidHom
          ⟨lL.val,d.normalizes_V (mem_sup_left lL.property)⟩ v = v := by
        apply Subtype.ext
        change l * v.val * l⁻¹ = v.val
        rw [← mem_centralizer_iff.mp hl.2 v.val v.property,mul_inv_cancel_right]
      rw [hc] at he
      change (d.coordinate v).toAdd = _ at he
      rw [show (d.coordinate v).toAdd = w from hv] at he
      simpa only [Section08.ComponentSieve.SixAndG2.NaturalSix.alternatingAction,
        QuotientGroup.mk'_apply,map_one,Module.End.one_apply] using he.symm
    exact ⟨lL,(QuotientGroup.eq_one_iff lL).mp hq,rfl⟩
  · rintro _ ⟨l,hl,rfl⟩
    refine ⟨l.property,?_⟩
    apply mem_centralizer_iff.mpr
    intro v hv
    have he := d.conjugation l ⟨v,hv⟩
    have hq : QuotientGroup.mk' (centralCore L) l = 1 := (QuotientGroup.eq_one_iff l).mpr hl
    rw [hq,map_one,map_one,Module.End.one_apply] at he
    have he' := congrArg (fun v : V => v.val) (d.coordinate.injective he)
    change l.val * v * l.val⁻¹ = v at he'
    exact (mul_inv_eq_iff_eq_mul.mp he').symm

/-- The action kernel is central modulo O₂(L), including the central
three-cover case. -/
theorem natural_kernel_commutator :
    ⁅L ⊓ centralizer (V : Set G),L⁆ ≤ L.pCoreIn 2 := by
  rw [natural_action_kernel d]
  apply commutator_le.mpr
  rintro x ⟨a,ha,rfl⟩ y hy
  let b : L := ⟨y,hy⟩
  let q := QuotientGroup.mk' (pCore 2 L)
  have hcenter : q a ∈ center (L ⧸ pCore 2 L) := ha
  have hcomm : q ⁅a,b⁆ = 1 := by
    rw [map_commutatorElement]
    apply commutatorElement_eq_one_iff_commute.mpr
    exact (mem_center_iff.mp hcenter (q b)).symm
  exact ⟨⁅a,b⁆,(QuotientGroup.eq_one_iff _).mp hcomm,rfl⟩

/-- A two-perfect actor centralizing the original hyperplane has trivial
action on V, once the earlier TI theorem places it in N_G(V). -/
theorem twoPerfect_seed_centralizer_fixes_module (Y : Subgroup G)
    (hY : IsPPerfect 2 Y) (hYM : Y ≤ M)
    (hYC : Y ≤ centralizer (U : Set G))
    (hTI : ∀ g ∈ normalizer (L : Set G),
      V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
        V.map (MulAut.conj g).toMonoidHom = V) :
    Y ≤ centralizer (V : Set G) := by
  let := d.chosen.elementary
  have hU : U ≠ ⊥ := by intro he; have hc := d.seed_card; simp [he] at hc
  have hYN : Y ≤ normalizer (V : Set G) := by
    intro y hy
    apply inf_centralizer_le_normalizer_of_trivial_intersections hTI hU d.seed_le
    exact ⟨d.local_normalizer ▸ hYM hy,hYC hy⟩
  have hdisp : ⁅Y,V⁆ ≤ P := by
    rw [commutator_comm]
    exact (commutator_mono le_rfl (le_inf (le_inf hYM hYN) hYC)).trans
      (local_seed_centralizer_displacement d)
  let f : Y →* MulAut V := V.normalizerMonoidHom.comp
    (Y.subtype.codRestrict (normalizer (V : Set G)) (fun y => hYN y.property))
  have hp : IsPGroup 2 f.range := by
    rintro ⟨a,⟨y,rfl⟩⟩
    refine ⟨1,?_⟩
    apply Subtype.ext
    change (f y) ^ 2 = 1
    apply MulEquiv.ext
    intro v
    let c := f y v * v⁻¹
    have hc : c.val ∈ P := hdisp (commutator_mem_commutator y.property v.property)
    have hfix : f y c = c := by
      apply Subtype.ext
      change y.val * c.val * y.val⁻¹ = c.val
      rw [← mem_centralizer_iff.mp (hYC y.property) c.val
        (d.plane_le_seed (d.line_le_plane hc)),mul_inv_cancel_right]
    have hc2 : c * c = 1 := by
      have hh := IsElementaryAbelian.exponent_dvd_p 2 V
      have hpow := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hh c
      simpa only [pow_two] using hpow
    have he : f y v = c * v := by simp only [c,inv_mul_cancel_right]
    change f y (f y v) = v
    calc
      _ = f y (c * v) := congrArg (f y) he
      _ = c * (c * v) := by rw [map_mul,hfix,he]
      _ = v := by rw [← mul_assoc,hc2,one_mul]
  have hone := hY.hom_eq_one_of_isPGroup hp f.rangeRestrict
  intro y hy
  apply mem_centralizer_iff.mpr
  intro v hv
  have he : f ⟨y,hy⟩ = 1 := by
    have hh := congrArg (fun a : Y →* f.range => ((a ⟨y,hy⟩ : f.range) : MulAut V)) hone
    simpa only [MonoidHom.one_apply,Subgroup.coe_one,MonoidHom.coe_rangeRestrict] using hh
  have hh := congrArg (fun a : MulAut V => (a ⟨v,hv⟩).val) he
  change y * v * y⁻¹ = v at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

/-- The first-paragraph normalizer bound in 13.3.14(b). The two-perfect
subgroup is normal only in YT; no ambient subnormality is assumed. -/
theorem natural_twoPerfect_normalizer_control [Group.IsPerfect L]
    (Y : Subgroup G) (hY : IsPPerfect 2 Y) (hne : Y ≠ ⊥)
    (hTY : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hYM : Y ≤ M) (hYC : Y ≤ centralizer (U : Set G))
    (hTI : ∀ g ∈ normalizer (L : Set G),
      V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
        V.map (MulAut.conj g).toMonoidHom = V)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → L ⊔ (T : Subgroup G) ≤ N → N = M) :
    normalizer (Y : Set G) ≤ M := by
  have hYV := twoPerfect_seed_centralizer_fixes_module d Y hY hYM hYC hTI
  have hYL : Y ≤ normalizer (L : Set G) := by rw [← d.local_normalizer]; exact hYM
  have hLV : L ≤ normalizer (V : Set G) := le_sup_left.trans d.normalizes_V
  have hLC : L ≤ normalizer (centralizer (V : Set G) : Set G) :=
    hLV.trans ((normal_subgroupOf_iff_le_normalizer
      (Subgroup.centralizer_le_normalizer _)).mp inferInstance)
  have hcomm : ⁅L,Y⁆ ≤ L ⊓ centralizer (V : Set G) :=
    le_inf (le_normalizer_iff_commutator_le_left.mp hYL)
      ((commutator_mono le_rfl hYV).trans (le_normalizer_iff_commutator_le_right.mp hLC))
  have hdouble := (commutator_mono hcomm le_rfl).trans (natural_kernel_commutator d)
  have hLQ : L ≤ normalizer (L.pCoreIn 2 : Set G) := L.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image L (pCore 2 L))
  have hYQ := hYL.trans (normalizer_le_normalizer_characteristic_image L (pCore 2 L))
  have hcorecomm : ⁅L,Y⁆ ≤ L.pCoreIn 2 := by
    have hh := commutator_commutator_le_of_rotate_of_le_normalizer hLQ hLQ hYQ
      hdouble (by simpa only [commutator_comm Y L] using hdouble)
    rwa [L.commutator_eq_self] at hh
  have hQT : L.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hn : L ⊔ (T : Subgroup G) ≤ normalizer (L : Set G) :=
      sup_le L.le_normalizer d.normalizes_L
    apply (pCoreIn_mono_of_normalizes (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left) hn).trans
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right] using
      pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  have hLY : L ≤ normalizer (Y : Set G) :=
    normalizes_of_commutator_le_twoGroup L Y (L.pCoreIn 2) hY
      (isPGroup_pCoreIn 2 L) (hQT.trans hTY) hLQ hcorecomm
  let J := Y ⊔ (T : Subgroup G)
  have hPT : P ≤ (T : Subgroup G) :=
    d.line_le_plane.trans (d.plane_le_seed.trans (d.seed_le.trans d.chosen.le_sylow))
  have hPn : J ≤ normalizer (P : Set G) :=
    sup_le (hYC.trans ((centralizer_le (d.line_le_plane.trans d.plane_le_seed)).trans
      (Subgroup.centralizer_le_normalizer _))) d.line_stable
  have hPcore : P ≤ J.pCoreIn 2 := le_pCoreIn_of_normalizes
    (T.isPGroup'.to_le hPT) (hPT.trans le_sup_right) hPn
  have hJcore : J.pCoreIn 2 ≠ ⊥ := by
    intro he
    have hp : P = ⊥ := le_bot_iff.mp (hPcore.trans he.le)
    have hc := d.line_card
    simp [hp] at hc
  have hJ : J ∈ Chapter1.He G := Chapter1.lemma_1_1_4_6 T
    (d.counterexample.qtke.toIsQTKE.evenCharacteristic T) ⟨hJcore,fun _ ht => (show (T : Subgroup G) ≤ J from le_sup_right) ht⟩
  have hYn : (Y.subgroupOf J).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le Y.le_normalizer hTY)
  have hYe : Y ∈ Chapter1.He G :=
    Chapter1.lemma_1_1_3_1 hJ hne le_sup_left hYn.isSubnormal
  have hcore : Y.pCoreIn 2 ≠ ⊥ := by
    intro he
    apply hne
    apply le_bot_iff.mp
    intro y hy
    have hh := hYe ⟨hy,?_⟩
    · exact he ▸ hh
    · rw [he]
      exact by intro x hx; rw [mem_bot.mp hx]; simp
  have hncore := normalizer_le_normalizer_characteristic_image Y (pCore 2 Y)
  exact hncore.trans (normalizer_le_of_unique_maximalTwoLocal hunique
    (isPGroup_pCoreIn 2 Y) hcore ((sup_le hLY hTY).trans hncore))

/-- The actual centralizing residual cannot lie in M if it is nontrivial.
This is the first source reduction for Y=O²(C_G(<V₃^{G₁}>)). -/
theorem natural_centralizingResidual_not_le [Group.IsPerfect L]
    (hTI : ∀ g ∈ normalizer (L : Set G),
      V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
        V.map (MulAut.conj g).toMonoidHom = V)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → L ⊔ (T : Subgroup G) ≤ N → N = M)
    (hescape : ¬ H ≤ M)
    (hne : centralizingResidual (conjugateSpanBy U H) ≠ ⊥) :
    ¬ centralizingResidual (conjugateSpanBy U H) ≤ M := by
  intro hYM
  have hHN := normalizes_centralizingResidual U H
  have hTH : (T : Subgroup G) ≤ H := d.first_normalizer.symm ▸ d.line_stable
  have hn := natural_twoPerfect_normalizer_control d _ (centralizingResidual_isPPerfect _)
    hne (hTH.trans hHN) hYM (centralizingResidual_le_seed_centralizer U H) hTI hunique
  exact hescape (hHN.trans hn)

end CFSG.Quasithin.Chapter13.Section03.Noncentrality
