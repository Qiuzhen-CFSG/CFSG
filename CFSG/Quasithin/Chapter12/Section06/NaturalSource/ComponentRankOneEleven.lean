module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.ComponentRankOneParameters
public import Theory.SpecificGroups.PSL2.InvertedOrderBound

/-!
# The original selected component is PSL2(11)

Complete the rank-one inspection using the inner original module action.
Transport its reflected odd torus through the actual component model and
then into H/O2(H). The original pair theorem restricts inverted odd orders
to three or five, bounding the field by eleven; the cubic fixed-subgroup
congruence then gives eleven. This reaches the source parameter conclusion
without an additional chief-section assumption.

The faithful binary-section contradiction for PSL2(11), abelianness of
the point span, the later 12.6.27--34 arguments and universal natural
reduction remain open. All original point, quotient, action, TI and
nonsingular-centralizer hypotheses are retained here.
Source: Aschbacher--Smith, proof of 12.6.26, printed pp.832--833.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)
  (hz : z ≠ 1)
  (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
  (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
  (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
    Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
  {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
  (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H))
  (c : (D.fullSetup hZ T z).SelectedComponent H) (a : c.ActionMarking)



include hz hTV hTz hbound hH hn a in
/-- The actual odd PSL2 model has field order eleven. The reflected odd torus
uses the same original module involution and literal H-star conjugation. -/
theorem SourceHypothesis.original_linearTwo_parameter_eleven
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    {F : Type*} [Field F] [Finite F] {p n : ℕ}
    (hp : p.Prime) (ho : Odd p) (hn2 : n ≤ 2) (hF : Nat.card F = p^n)
    (e : Nonabelian.Setup.star H c.K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :
    Nat.card F = 11 := by
  obtain ⟨hp3,hn0,hmod⟩ := S.original_linearTwo_parameter_mod_twelve D hZ z hz hTV hTz
    hbound hH hn c a hTI hns hp ho hn2 hF e
  obtain ⟨b,hb,hb2,_,_⟩ := S.original_selectedComponent_model_fixed_cubic
    D hZ z hz hTV hTz hbound hH hn c a hTI hns e
  have hb2' : orderOf b = 2 := ((MulAut.congr e).orderOf_eq b).symm.trans hb2
  obtain ⟨t,ht⟩ := S.original_linearTwo_module_inner D hZ z hz hTV hTz hbound hH hn c a
    hTI hns hp ho hn2 hF e b hb hb2'
  have ht2 : orderOf t = 2 :=
    (MulAut.conj_orderOf_of_center_eq_bot (GorensteinWalter.psl2_center_eq_bot F) t).symm.trans
      (ht ▸ hb2)
  let : Fact p.Prime := ⟨hp⟩
  have hsmall : Nat.card F ≤ 11 := by
    apply Theory.PSL2.odd_field_card_le_eleven_of_inverted_orders ho hF t ht2
    intro y hy hoY hi
    let x := e.symm y
    have hiX : b x = x⁻¹ := by
      apply e.injective
      have hh : (MulAut.congr e b) y = y⁻¹ := by rw [ht]; exact hi
      change e (b (e.symm y)) = e ((e.symm y)⁻¹)
      change e (b (e.symm y)) = y⁻¹ at hh
      simpa only [map_inv,MulEquiv.apply_symm_apply] using hh
    obtain ⟨v,hv,he⟩ := hb
    let u := QuotientGroup.mk' (pCore 2 H) (inclusion a.local_le v)
    have hu : u ∈ Nonabelian.Setup.star H V := mem_map_of_mem _ hv
    have hxorder : orderOf (x : Nonabelian.Setup.Hstar H) = orderOf y :=
      (Subgroup.orderOf_coe x).trans (e.symm.orderOf_eq y)
    have hxne : (x : Nonabelian.Setup.Hstar H) ≠ 1 := by
      intro hh
      have hh' : x = 1 := Subtype.ext hh
      exact hy (by simpa only [x,map_one,MulEquiv.apply_symm_apply] using congrArg e hh')
    have hinv : u*x.val*u⁻¹=x.val⁻¹ := by
      rw [←a.conjugation v x,he]
      exact congrArg Subtype.val hiX
    have hord := S.original_star_inverted_odd_order D hZ z hz hTV hTz hbound hns hH
      u hu x.val hxne (hxorder ▸ hoY) hinv
    rwa [hxorder] at hord
  have hlarge : 3 < p^n := hp3.trans_le (Nat.le_pow hn0)
  omega

include hz hTV hTz hbound hH hn a in
/-- After the full original rank-one inspection, the selected component is
an actual PSL2(11), with its original quotient carrier retained. -/
theorem SourceHypothesis.original_selectedComponent_linearTwoEleven
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L) :
    ClassicalGroup.IsPSL (Nonabelian.Setup.star H c.K) 2 11 := by
  obtain ⟨p,n,hp,ho,hn2,F,hfield,hfinite,hF,⟨e⟩⟩ :=
    S.original_selectedComponent_oddLinearTwo D hZ z hz hTV hTz hbound hH hn c a hTI hns
  let := hfield
  let := hfinite
  exact ⟨F,inferInstance,inferInstance,
    S.original_linearTwo_parameter_eleven D hZ z hz hTV hTz hbound hH hn c a hTI hns hp ho hn2 hF e,
    ⟨e⟩⟩

end CFSG.Quasithin.Chapter12.Section06
