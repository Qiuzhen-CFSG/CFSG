module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddCriticalPair.Coordinates.Decomposition
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentCriticalPair.ResidualCoordinates.Lift

/-!
# Nonzero projections of the original orthogonal seed

The genuine factor exchanger in T exchanges both covering planes. If the
T-normalized seed had zero projection on either plane, it would lie in the
full fixed preimage C after applying that same exchanger. Its H-span would
then be fixed, contradicting the nontrivial orthogonal moved module.

The conclusion retains v=b₁*b₂*c with c in C and both bᵢ nonzero modulo Z.
This is the seed decomposition used by Coordinates.Source, without identifying
either lift with the independently selected suitable element u.

Source: Aschbacher--Smith 14.6.17(5), printed p.1036.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06.OddCriticalPair
open Chapter15.Section03 OddNormalizer OrthogonalSource
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
variable {G : Type*} [Group G]
variable {H U Z : Subgroup G} [IsElementaryAbelian 2 U]

private theorem mem_sup_in_module {A B : Subgroup G} (hAU : A ≤ U) (hBU : B ≤ U)
    {v : G} (hv : v ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, a*b=v := by
  have hvU := (sup_le hAU hBU) hv
  have hv' : (⟨v,hvU⟩ : U) ∈ A.subgroupOf U ⊔ B.subgroupOf U := by
    rw [←subgroupOf_sup hAU hBU]
    exact hv
  obtain ⟨a,ha,b,hb,he⟩ := mem_sup_of_normal_right.mp hv'
  exact ⟨a,ha,b,hb,congrArg Subtype.val he⟩

/-- The central line belongs to the full preimage of the fixed quotient space. -/
theorem point_le_fixedSupport (a : LocalQuotientAction H U Z) : Z ≤ fixedSupport a := by
  intro z hz
  apply (mem_supportPreimage a _ ⟨z,a.kernel_le hz⟩).mpr
  have he : QuotientGroup.mk' (Z.subgroupOf U) ⟨z,a.kernel_le hz⟩ = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hz
  rw [he]
  exact (fixedSpace a.representation ⊤).zero_mem

/-- The full fixed preimage is normalized even though its elements need only
be fixed modulo the source line by H. -/
theorem fixedSupport_normalized (a : LocalQuotientAction H U Z) :
    H ≤ normalizer (fixedSupport a : Set G) :=
  le_normalizer_iff_commutator_le_left.mpr
    ((fixedSupport_commutator a).trans (point_le_fixedSupport a))

private theorem fixed_sup_intersection (a : LocalQuotientAction H U Z)
    (o : SourceOrthogonalFourAction H U Z (H.pCoreIn 2))
    (i j : OrthogonalPlaneIndex) (hji : j ≠ i) :
    (o.plane i ⊔ fixedSupport a) ⊓ (o.plane j ⊔ fixedSupport a) ≤ fixedSupport a := by
  intro v hv
  have hKU : ⁅U,H⁆ ≤ U := le_normalizer_iff_commutator_le_left.mp o.normalized
  obtain ⟨b,hb,c,hc,he⟩ := mem_sup_in_module ((o.plane_le i).trans hKU)
    (supportPreimage_le a _) hv.1
  have hb' : b ∈ o.plane j ⊔ fixedSupport a := by
    have hh := (o.plane j ⊔ fixedSupport a).mul_mem hv.2
      ((le_sup_right : fixedSupport a ≤ o.plane j ⊔ fixedSupport a) ((fixedSupport a).inv_mem hc))
    simpa only [←he,mul_inv_cancel_right] using hh
  exact he ▸ (fixedSupport a).mul_mem
    (point_le_fixedSupport a (first_plane_separated_fixed a o i j hji ⟨hb,hb'⟩)) hc

variable [Finite G]

/-- The original exchanged-factor element exchanges the two literal covering
planes, with one and the same left conjugator in T. -/
theorem original_exchanged_planes
    (a : LocalQuotientAction H U Z) (T H0 H1 H2 : Subgroup G) (hTH : T ≤ H)
    (d : ExchangedFactorSetup a T 3 H0 H1 H2)
    (o : SourceOrthogonalFourAction H U Z (H.pCoreIn 2)) (hZ : Nat.card Z = 2)
    (i j : OrthogonalPlaneIndex) (hji : j ≠ i) (hi : o.plane i = firstSupport a H1) :
    ∃ x ∈ T, (o.plane i).map (MulAut.conj x).toMonoidHom = o.plane j ∧
      (o.plane j).map (MulAut.conj x).toMonoidHom = o.plane i := by
  obtain ⟨x,hx,_,hex⟩ := d.exchanged
  let xH : H := ⟨x⁻¹,H.inv_mem (hTH hx)⟩
  have ht : (firstSupport a H1).map (MulAut.conj x⁻¹).toMonoidHom = firstSupport a H2 := by
    unfold firstSupport
    rw [supportPreimage_conjugate a _ xH,moved_map_conjugate,
      ←actorImage_conjugate H1 (d.first_le.trans d.zero_le) xH]
    change supportPreimage a (subspaceCommutator a.representation ⊤
      (actorImage H (H1.map (MulAut.conj x⁻¹).toMonoidHom))) = _
    rw [hex]
  have hj := original_second_support_eq a T H0 H1 H2 hTH d o hZ i j hji hi
  have hab : (o.plane i).map (MulAut.conj x⁻¹).toMonoidHom = o.plane j := by
    rw [hi,ht,hj]
  have hp := o.plane_conjugate hZ i xH
  have hs : (o.actor xH).right * i = j := by
    by_contra hn
    have htwo : ∀ i j k : OrthogonalPlaneIndex, j ≠ i → k ≠ j → k = i := by decide
    rw [htwo i j _ hji hn,hab] at hp
    have hc := o.planes_inf_eq i j hji
    rw [hp,inf_idem] at hc
    have hc' := congrArg (fun A : Subgroup G => Nat.card A) hc
    rw [o.card_plane hZ,hZ] at hc'
    omega
  have hs' : (o.actor xH).right*j = i := by
    have htwo : ∀ s i j : OrthogonalPlaneIndex, j ≠ i → s*i=j → s*j=i := by decide
    exact htwo _ _ _ hji hs
  refine ⟨x⁻¹,T.inv_mem hx,hab,?_⟩
  exact (o.plane_conjugate hZ j xH).trans (congrArg o.plane hs')

/-- A T-normalized seed which generates U has a nonzero projection on both
exchanged planes. Its fixed supplement is retained in the decomposition. -/
theorem orthogonal_seed_decomposition
    (a : LocalQuotientAction H U Z) (T V H0 H1 H2 : Subgroup G) (hTH : T ≤ H)
    (d : ExchangedFactorSetup a T 3 H0 H1 H2)
    (o : SourceOrthogonalFourAction H U Z (H.pCoreIn 2)) (hZ : Nat.card Z = 2)
    (i j : OrthogonalPlaneIndex) (hji : j ≠ i) (hi : o.plane i = firstSupport a H1)
    (hVU : V ≤ U) (hZV : Z ≤ V) (hVcard : Nat.card V = 4)
    (hTV : T ≤ normalizer (V : Set G)) (hgen : conjugateSpanBy V H = U)
    (hcover : U = o.plane i ⊔ o.plane j ⊔ fixedSupport a) :
    ∃ v ∈ V, v ∉ Z ∧ ∃ b₁ ∈ o.plane i, b₁ ∉ Z ∧
      ∃ b₂ ∈ o.plane j, b₂ ∉ Z ∧ ∃ c ∈ fixedSupport a, v = b₁*b₂*c := by
  have hKU : ⁅U,H⁆ ≤ U := le_normalizer_iff_commutator_le_left.mp o.normalized
  have hVC : ¬V ≤ fixedSupport a := by
    intro hv
    have hUC := conjugateSpanBy_le hv (fixedSupport_normalized a)
    rw [hgen] at hUC
    have hKZ : ⁅U,H⁆ ≤ Z := fun x hx => moved_inf_fixedSupport_le a o ⟨hx,hUC (hKU hx)⟩
    have hh := card_le_of_le ((o.plane_le i).trans hKZ)
    rw [o.card_plane hZ,hZ] at hh
    omega
  obtain ⟨x,hx,hAB,hBA⟩ := original_exchanged_planes a T H0 H1 H2 hTH d o hZ i j hji hi
  have hVx := mem_normalizer_iff_map_conj_eq.mp (hTV hx)
  change V.map (MulAut.conj x).toMonoidHom = V at hVx
  have hCx := mem_normalizer_iff_map_conj_eq.mp (fixedSupport_normalized a (hTH hx))
  change (fixedSupport a).map (MulAut.conj x).toMonoidHom = fixedSupport a at hCx
  have hVA : ¬V ≤ o.plane i ⊔ fixedSupport a := by
    intro ha
    have hb := map_mono (f := (MulAut.conj x).toMonoidHom) ha
    rw [hVx,Subgroup.map_sup,hAB,hCx] at hb
    exact hVC ((le_inf ha hb).trans (fixed_sup_intersection a o i j hji))
  have hVB : ¬V ≤ o.plane j ⊔ fixedSupport a := by
    intro hb
    have ha := map_mono (f := (MulAut.conj x).toMonoidHom) hb
    rw [hVx,Subgroup.map_sup,hBA,hCx] at ha
    exact hVC ((le_inf ha hb).trans (fixed_sup_intersection a o i j hji))
  have hVZ : ¬V ≤ Z := by
    intro hle
    have hh := card_le_of_le hle
    rw [hVcard,hZ] at hh
    omega
  obtain ⟨v,hv,hvz⟩ := Set.not_subset.mp hVZ
  have hseed := ComponentCriticalPair.plane_eq_line_sup_zpowers hVcard hZ hZV v hv hvz
  have hvcover : v ∈ o.plane i ⊔ o.plane j ⊔ fixedSupport a := hcover.le (hVU hv)
  obtain ⟨w,hw,c,hc,he⟩ := mem_sup_in_module
    (sup_le ((o.plane_le i).trans hKU) ((o.plane_le j).trans hKU))
    (supportPreimage_le a _) hvcover
  obtain ⟨b₁,hb₁,b₂,hb₂,he'⟩ := mem_sup_in_module
    ((o.plane_le i).trans hKU) ((o.plane_le j).trans hKU) hw
  have he'' : v = b₁*b₂*c := he.symm.trans (congrArg (·*c) he'.symm)
  have hb₁z : b₁ ∉ Z := by
    intro hz
    apply hVB
    rw [hseed]
    refine sup_le ((o.point_le_plane j).trans le_sup_left) (zpowers_le.mpr ?_)
    rw [he'']
    exact (o.plane j ⊔ fixedSupport a).mul_mem
      ((le_sup_left : o.plane j ≤ o.plane j ⊔ fixedSupport a)
        ((o.plane j).mul_mem (o.point_le_plane j hz) hb₂))
      ((le_sup_right : fixedSupport a ≤ o.plane j ⊔ fixedSupport a) hc)
  have hb₂z : b₂ ∉ Z := by
    intro hz
    apply hVA
    rw [hseed]
    refine sup_le ((o.point_le_plane i).trans le_sup_left) (zpowers_le.mpr ?_)
    rw [he'']
    exact (o.plane i ⊔ fixedSupport a).mul_mem
      ((le_sup_left : o.plane i ≤ o.plane i ⊔ fixedSupport a)
        ((o.plane i).mul_mem hb₁ (o.point_le_plane i hz)))
      ((le_sup_right : fixedSupport a ≤ o.plane i ⊔ fixedSupport a) hc)
  exact ⟨v,hv,hvz,b₁,hb₁,hb₁z,b₂,hb₂,hb₂z,c,hc,he''⟩

end CFSG.Quasithin.Chapter14.Section06.OddCriticalPair
