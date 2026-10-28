module
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.EarlierResidual.Ordinary
public import Theory.ThreeSubgroups
/-!
# Prime divisors of the covered point residual

The point action has only primes two and three. Its kernel commutes with L
modulo O₂(L): the kernel inside L is central modulo that core, and L is
perfect, so the three-subgroups lemma removes the central factor. The
prime-set residual is then normalized on both sides of the original
core-free join and vanishes by characteristic two of the outside group.

Source: Aschbacher--Smith 13.3.8--9, printed pp.886--887.
-/

public section
open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter13.Section08.Components.EarlierResidual
open TransvectionRecognition.Component.ModelExtension SourceCompletion
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ : Subgroup G}
  (d : LocalSetup T L V V₁ V₂ V₃ M G₁)

include d

theorem covered_point_kernel_commutator (C : Subgroup G) (hCV : C ≤ centralizer (V:Set G))
    (hCL : C ≤ normalizer (L:Set G)) : ⁅L,C⁆ ≤ L.pCoreIn 2 := by
  let : Group.IsPerfect (L.subgroupOf (L ⊔ (T:Subgroup G))) :=
    d.counterexample.local_component.1.1.perfect
  let e : L.subgroupOf (L ⊔ (T:Subgroup G)) ≃* L := subgroupOfEquivOfLe le_sup_left
  let : Group.IsPerfect L := Group.IsPerfect.ofSurjective (f:=e.toMonoidHom) e.surjective
  have hLC : ⁅L,C⁆ ≤ L ⊓ centralizer (V:Set G) :=
    le_inf (le_normalizer_iff_commutator_le_left.mp hCL)
      ((commutator_mono le_rfl hCV).trans
        (le_normalizer_iff_commutator_le_right.mp
          ((le_sup_left.trans d.normalizes_V).trans
            ((normal_subgroupOf_iff_le_normalizer (centralizer_le_normalizer (V:Set G))).mp
              inferInstance))))
  have hdouble : ⁅⁅L,C⁆,L⁆ ≤ L.pCoreIn 2 := by
    apply commutator_le.mpr
    intro x hx l hl
    let xL : L := ⟨x,(hLC hx).1⟩
    let lL : L := ⟨l,hl⟩
    have hxZ : QuotientGroup.mk' (pCore 2 L) xL ∈ center (L ⧸ pCore 2 L) := by
      change xL ∈ centralCore L
      rw [d.centralCore_eq_centralizer]
      exact (hLC hx).2
    have he : ⁅xL,lL⁆ ∈ pCore 2 L := by
      apply (QuotientGroup.eq_one_iff _).mp
      change QuotientGroup.mk' (pCore 2 L) ⁅xL,lL⁆ = 1
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact (mem_center_iff.mp hxZ _).symm
    exact ⟨⁅xL,lL⁆,he,rfl⟩
  have hLQ : L ≤ normalizer (L.pCoreIn 2:Set G) := L.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image L (pCore 2 L))
  have hCQ := hCL.trans (normalizer_le_normalizer_characteristic_image L (pCore 2 L))
  have hh := commutator_commutator_le_of_rotate_of_le_normalizer hLQ hLQ hCQ
    hdouble (by simpa only [commutator_comm C L] using hdouble)
  rwa [L.commutator_eq_self] at hh

open Section03.PointResidualImage
open BinaryPermutation Representation.BinaryOffender
open TransvectionQuotients.FiveSeed TransvectionQuotients.FiveSeed.BarMarking
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open scoped IsMulCommutative

omit d in
private theorem point_isTwoThree (P:Submodule (ZMod 2) NaturalGeometry.V)
    (hP:Module.finrank (ZMod 2) P=1) :
    IsPiGroup twoThreePrimes (subspaceStabilizer (naturalRepresentation (Fin 6)) P) := by
  let J:=subspaceStabilizer (naturalRepresentation (Fin 6)) P
  let T:Sylow 2 J:=Classical.choice inferInstance
  have hi:(T:Subgroup J).index=3 := by
    have hJ:(⊤:Subgroup S)⊓subspaceStabilizer (naturalRepresentation (Fin 6)) P=J := inf_of_le_right le_top
    have hh:=point_sylow_index_three (⊤:Subgroup S) (by simp) P hP
    rw [hJ] at hh
    exact hh T
  obtain ⟨n,hn⟩:=T.isPGroup'.exists_card_eq
  have hc:Nat.card J=2^n*3 := by rw [←(T:Subgroup J).card_mul_index,hn,hi]
  rw [IsPiGroup_iff]
  intro p hd
  change p.val=2 ∨ p.val=3
  change p.val∣Nat.card J at hd
  rw [hc] at hd
  rcases p.property.dvd_mul.mp hd with hd|hd
  · exact Or.inl (((Nat.dvd_prime Nat.prime_two).mp (p.property.dvd_of_dvd_pow hd)).resolve_left p.property.ne_one)
  · exact Or.inr (((Nat.dvd_prime Nat.prime_three).mp hd).resolve_left p.property.ne_one)

omit d in
private theorem twoThree_of_point_commutator {G:Type*} [Group G] [Finite G]
    (M L V H Y:Subgroup G) [IsElementaryAbelian 2 V]
    (hLP:L≤M⊓normalizer (V:Set G))
    (hPL:M⊓normalizer (V:Set G)≤normalizer (L:Set G))
    (α:L→*alternatingGroup (Fin 6)) (hα:Function.Surjective α)
    (e:Additive V≃ₗ[ZMod 2] natural (Fin 6))
    (he:∀ (l:L) (v:Additive V), e (conjugationRepresentation
      (M⊓normalizer (V:Set G)) V inf_le_right (inclusion hLP l) v)=
      alternatingNaturalRepresentation (Fin 6) (α l) (e v))
    (hcomm:⁅L,(M⊓normalizer (V:Set G))⊓centralizer (V:Set G)⁆≤L.pCoreIn 2)
    (hY:Y≤M⊓normalizer (V:Set G)) (hYH:Y≤H) (hnY:H≤normalizer (Y:Set G))
    (hQH:L.pCoreIn 2≤H) (hcore:pCore 2 (L⊔H:Subgroup G)=⊥)
    (hchar:centralizer (pCore 2 H:Set H)≤pCore 2 H)
    (w:Additive V) (hw:w≠0) (hc:Y≤centralizer ({(w.toMul:G)}:Set G)) :
    IsPiGroup twoThreePrimes Y := by
  let P:=M⊓normalizer (V:Set G)
  obtain ⟨f,_hfL,hact,hker⟩:=natural_extension P L V hLP hPL inf_le_right α hα e he
  let a:Y→*S:=f.comp (inclusion hY)
  let line:=Submodule.span (ZMod 2) {e w}
  have hew:e w≠0 := by
    intro hh
    exact hw (e.injective (hh.trans e.map_zero.symm))
  have hline:Module.finrank (ZMod 2) line=1:=finrank_span_singleton hew
  have hstab:a.range≤subspaceStabilizer (naturalRepresentation (Fin 6)) line := by
    apply le_subspaceStabilizer
    rintro _ ⟨y,rfl⟩ v hv
    obtain ⟨c,rfl⟩:=Submodule.mem_span_singleton.mp hv
    have hfix:conjugationRepresentation P V inf_le_right (inclusion hY y) w=w := by
      apply Additive.toMul.injective
      apply Subtype.ext
      change (y:G)*(w.toMul:G)*(y:G)⁻¹=(w.toMul:G)
      have hh:=mem_centralizer_singleton_iff.mp (hc y.property)
      rw [hh,mul_inv_cancel_right]
    have hf:naturalRepresentation (Fin 6) (a y) (e w)=e w := by
      change naturalRepresentation (Fin 6) (f (inclusion hY y)) (e w)=e w
      rw [←hact,hfix]
    simpa only [map_smul,hf] using Submodule.smul_mem line c
      (Submodule.mem_span_singleton_self (e w))
  have hpi:IsPiGroup twoThreePrimes a.range :=
    (point_isTwoThree line hline).of_injective (inclusion hstab) (inclusion_injective hstab)
  have hres:piResidual twoThreePrimes Y≤a.ker :=
    piResidual_le_ker_of_range twoThreePrimes a hpi
  let N:=(piResidual twoThreePrimes Y).map Y.subtype
  have hNP:N≤P:=(map_subtype_le _).trans hY
  have hfN (n:G) (hn:n∈N):f ⟨n,hNP hn⟩=1 := by
    obtain ⟨y,hy,rfl⟩:=hn
    exact hres hy
  apply twoThree_of_residual_commutator L H Y (L.pCoreIn 2) hYH hnY hQH
    (isPGroup_pCoreIn 2 L)
    (L.le_normalizer.trans (normalizer_le_normalizer_characteristic_image L (pCore 2 L)))
    ?_ hcore hchar
  apply (commutator_mono le_rfl (le_inf hNP ?_)).trans hcomm
  intro n hn
  have hh : (⟨n,hNP hn⟩:P) ∈ f.ker := hfN n hn
  rw [hker] at hh
  exact hh

/-- The covered point case of 13.3.8(2), with the actual outside overgroup. -/
theorem covered_twoThree
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    {J Y : Subgroup G}
    (hJ : J ∈ Chapter1.HOutside G (T:Set G) (M:Set G))
    (hYJ : Y ≤ J) (hn : (Y.subgroupOf J).Normal)
    (v : G) (hv : v∈V₁) (hne : v∉V⊓centralizer (L:Set G))
    (hfix : Y ≤ M⊓centralizer ({v}:Set G)) : IsPiGroup twoThreePrimes Y := by
  let := local_elementary d
  let α := d.local_quotient.toMonoidHom.comp (QuotientGroup.mk' (centralCore L))
  have hα : Function.Surjective α := d.local_quotient.surjective.comp (QuotientGroup.mk'_surjective _)
  let e : Additive V ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 6) :=
    d.coordinate.toAdditiveLeft.toLinearEquiv (ZMod.map_smul _)
  have hLP : L ≤ M⊓normalizer (V:Set G) :=
    le_inf (d.local_normalizer.symm ▸ L.le_normalizer) (le_sup_left.trans d.normalizes_V)
  have hPL : M⊓normalizer (V:Set G) ≤ normalizer (L:Set G) := by
    rw [←d.local_normalizer]; exact inf_le_left
  have hY : Y ≤ M⊓normalizer (V:Set G) :=
    le_inf (hfix.trans inf_le_left) (hfix.trans (source_point_normalizes d hv hne))
  have hnY : J ≤ normalizer (Y:Set G) := (normal_subgroupOf_iff_le_normalizer hYJ).mp hn
  have hQT : L.pCoreIn 2 ≤ T := (isPGroup_pCoreIn 2 L).le_sylow_of_normalized T
    (d.normalizes_L.trans (normalizer_le_normalizer_characteristic_image L (pCore 2 L)))
  have hvV : v∈V := (d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le)) hv
  have hv0 : v≠1 := by intro he; exact hne (he ▸ one_mem _)
  let w : Additive V := Additive.ofMul ⟨v,hvV⟩
  have hw : w≠0 := by
    intro he
    exact hv0 (congrArg (fun z:Additive V => z.toMul.val) he)
  exact twoThree_of_point_commutator M L V J Y hLP hPL α hα e
    (fun l w => d.conjugation l w.toMul)
    (covered_point_kernel_commutator d _ inf_le_right (inf_le_left.trans hPL))
    hY hYJ hnY (hQT.trans hJ.1.2) (outside_join_core d h hJ)
    (outside_characteristic_two h hJ) w hw (hfix.trans inf_le_right)
end CFSG.Quasithin.Chapter13.Section08.Components.EarlierResidual
