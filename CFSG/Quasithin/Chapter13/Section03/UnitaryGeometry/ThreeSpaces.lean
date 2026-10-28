module

public import CFSG.Quasithin.Chapter13.Section03.UnitaryGeometry.ModelReduction
public import Theory.Representation.G2BinaryIsotropicThree.Orbits
public import Theory.Representation.G2BinaryNaturalNormalizer

/-!
# Original-group isotropic three-space escape in the unitary branch

The actual automizer chart turns a faithful pointwise model stabilizer into
C_M(U)=C_M(V). The E.6.11(2) action-escape input then excludes that branch when
r=3. The remaining derived-group conjugator lifts through the original
normalizer, giving escape for the literal marked V₃. A final application derives
the entire ambient embedding from the earlier normal G₂(2)′ natural-module
marking; no ambient-image or conjugator-lift conclusion is assumed.

The primary nondegenerate-plane centralizer bound from 13.3.12(2), and the
actual E.6.11(2) action conclusion, remain explicit earlier-source inputs.
Their full source producers are separate outstanding steps.

Source: Aschbacher–Smith 13.3.12(3), printed p.890, and E.6.11–12, p.250.
-/

public section

open Subgroup Module
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.UnitaryGeometry
open ChapterE Atlas.G2.Natural.BinaryNondegeneratePlane
open Atlas.G2.Natural.BinaryIsotropicThree
variable {G : Type*} [Group G] [Finite G] {V M : Subgroup G} [IsElementaryAbelian 2 V]
  {K₀ : GroupClass} {T : Sylow 2 G}

theorem localCentralizer_eq_of_pointwise_faithful
    (h : ChapterE.Section06.HypothesisE61 K₀ T M V)
    (E : Additive V≃ₗ[ZMod 2] W)
    (f : Automizer V→*Atlas.G2.Model K) (hf : Function.Injective f)
    (he : ∀a v,E (automizerRepresentation V a v)=rho (f a) (E v))
    (U : Subgroup G) (hU : U≠⊥) (hUV : U≤V)
    (hfix : ∀a : Atlas.G2.Model K,
      (∀v∈(ambientSpace (V:=V) U).map E.toLinearMap,rho a v=v)→a=1) :
    M⊓centralizer (U:Set G)=M⊓centralizer (V:Set G) := by
  apply le_antisymm
  · intro x hx
    refine ⟨hx.1,?_⟩
    let n : normalizer (V:Set G) := ⟨x,h.localCentralizer_le_normalizer hU hUV hx⟩
    let a : Automizer V := V.normalizerMonoidHom.rangeRestrict n
    have ha : f a=1 := hfix (f a) (by
      rintro v ⟨u,hu,rfl⟩
      change rho (f a) (E u)=E u
      rw [←he a u]
      apply congrArg E
      change V.normalizerMonoidHom n u.toMul=u.toMul
      apply Subtype.ext
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      have hcomm := (Subgroup.mem_centralizer_iff.mp hx.2) u.toMul.val (show u.toMul.val∈U from hu)
      change u.toMul.val*x=x*u.toMul.val at hcomm
      rw [←hcomm,mul_inv_cancel_right])
    have ha1 : a=1 := hf (ha.trans (map_one f).symm)
    have hn : n∈V.normalizerMonoidHom.ker := congrArg Subtype.val ha1
    rwa [Subgroup.normalizerMonoidHom_ker] at hn
  · exact inf_le_inf_left M (Subgroup.centralizer_le hUV)

theorem natural_source_three_space_orbit
    (h : ChapterE.Section06.HypothesisE61 K₀ T M V)
    (E : Additive V≃ₗ[ZMod 2] W)
    (f : Automizer V→*Atlas.G2.Model K) (hf : Function.Injective f)
    (he : ∀a v,E (automizerRepresentation V a v)=rho (f a) (E v))
    (hFour : ∀l : Subgroup G,l≤V → Nat.card l=4 →
      ((markedForm E).restrict (ambientSpace (V:=V) l)).Nondegenerate → centralizer (l:Set G)≤M)
    (hact : ∀U∈ChapterE.Section06.obstructionFamily M V,
      (∀X : Subgroup G,U<X→X≤V→centralizer (X:Set G)≤M)→
      1<subgroupCorank V U→∃x∈M⊓centralizer (U:Set G),x∉centralizer (V:Set G))
    (hr : globalR V=3) :
    ∃U : Subgroup G,U≤V ∧ ¬centralizer (U:Set G)≤M ∧
      ∃g : commutator (Atlas.G2.Model K),
        ((ambientSpace (V:=V) U).map E.toLinearMap).map (rho g.val)=target false := by
  obtain ⟨U,hUV,hd,hi,hes⟩ := natural_source_three_space_reduction h E hFour hr
  let P := (ambientSpace (V:=V) U).map E.toLinearMap
  have hdim : finrank K P=3 := (E.finrank_map_eq _).trans hd
  have hiso : ∀v∈P,∀w∈P,form v w=0 := by
    rintro v ⟨x,hx,rfl⟩ w ⟨y,hy,rfl⟩
    exact hi x hx y hy
  rcases derived_orbit_or_pointwise_faithful P hiso hdim with horb|hfaith
  · exact ⟨U,hUV,hes,horb⟩
  · have hU : U≠⊥ := by
      intro hu
      have hc := ambientSpace_finrank_add_corank (V:=V) U
      rw [hu,ChapterE.Section06.corank_bot] at hc
      have hz : finrank (ZMod 2) (ambientSpace (V:=V) U)=0 := by
        rw [hu]
        omega
      omega
    have hc := localCentralizer_eq_of_pointwise_faithful h E f hf he U hU hUV hfaith
    obtain ⟨_,_,_,_,_,heq⟩ := h.hyperplane_escape_of_maximal_action hact hU hUV hc hes
    rw [hr] at heq
    norm_num at heq
omit [Finite G] in
theorem ambientGroup_ambientSpace {U : Subgroup G} (hUV : U≤V) :
    ambientGroup (ambientSpace (V:=V) U)=U := by
  unfold ambientGroup ambientSpace
  rw [subgroupSpace.symm_apply_apply]
  exact Subgroup.map_subgroupOf_eq_of_le hUV

omit [Finite G] in
theorem ambientSpace_conjugate {U : Subgroup G} (hUV : U≤V)
    (n : normalizer (V:Set G)) :
    ambientSpace (V:=V) (U.map (MulAut.conj n.val).toMonoidHom)=
      (ambientSpace (V:=V) U).map
        (automizerRepresentation V (V.normalizerMonoidHom.rangeRestrict n)) := by
  ext v
  constructor
  · intro hv
    change v.toMul.val∈U.map (MulAut.conj n.val).toMonoidHom at hv
    obtain ⟨u,hu,he⟩ := hv
    refine ⟨Additive.ofMul ⟨u,hUV hu⟩,hu,?_⟩
    apply Additive.toMul.injective
    apply Subtype.ext
    exact he
  · rintro ⟨u,hu,he⟩
    change v.toMul.val∈U.map (MulAut.conj n.val).toMonoidHom
    refine ⟨u.toMul.val,hu,?_⟩
    exact congrArg (fun z : Additive V=>z.toMul.val) he

noncomputable def standardThree (E : Additive V≃ₗ[ZMod 2] W) : Subgroup G :=
  ambientGroup ((target false).comap E.toLinearMap)

theorem natural_source_standard_three_escape
    (h : ChapterE.Section06.HypothesisE61 K₀ T M V)
    (E : Additive V≃ₗ[ZMod 2] W)
    (f : Automizer V→*Atlas.G2.Model K) (hf : Function.Injective f)
    (he : ∀a v,E (automizerRepresentation V a v)=rho (f a) (E v))
    (hderived : ∀g : commutator (Atlas.G2.Model K),∃a : Automizer V,f a=g.val)
    (hFour : ∀l : Subgroup G,l≤V → Nat.card l=4 →
      ((markedForm E).restrict (ambientSpace (V:=V) l)).Nondegenerate → centralizer (l:Set G)≤M)
    (hact : ∀U∈ChapterE.Section06.obstructionFamily M V,
      (∀X : Subgroup G,U<X→X≤V→centralizer (X:Set G)≤M)→
      1<subgroupCorank V U→∃x∈M⊓centralizer (U:Set G),x∉centralizer (V:Set G))
    (hr : globalR V=3) : ¬centralizer (standardThree E:Set G)≤M := by
  obtain ⟨U,hUV,hes,g,hshape⟩ := natural_source_three_space_orbit h E f hf he hFour hact hr
  obtain ⟨a,ha⟩ := hderived g
  obtain ⟨n,hn⟩ := a.property
  have hn' : V.normalizerMonoidHom.rangeRestrict n=a := Subtype.ext hn
  let U' := U.map (MulAut.conj n.val).toMonoidHom
  have hU' : U'≤V := by
    have hh := Subgroup.map_mono (f:=(MulAut.conj n.val).toMonoidHom) hUV
    exact hh.trans_eq (Subgroup.mem_normalizer_iff_map_conj_eq.mp n.property)
  have hchart : (ambientSpace (V:=V) U').map E.toLinearMap=target false := by
    rw [show ambientSpace (V:=V) U'=(ambientSpace (V:=V) U).map
      (automizerRepresentation V a) by rw [ambientSpace_conjugate hUV n,hn']]
    rw [←Submodule.map_comp]
    have hlin : E.toLinearMap.comp (automizerRepresentation V a)=(rho (f a)).comp E.toLinearMap := by
      apply LinearMap.ext
      intro v
      exact he a v
    rw [hlin,Submodule.map_comp,ha]
    exact hshape
  have hspaces : ambientSpace (V:=V) U'=(target false).comap E.toLinearMap := by
    rw [←hchart,Submodule.comap_map_eq_of_injective E.injective]
  have hgroup : U'=standardThree E := by
    rw [←ambientGroup_ambientSpace hU',hspaces]
    rfl
  intro hc
  apply hes
  intro c hcU
  have hnM : n.val∈M := h.normalizer_le n.property
  have hh : n.val*c*n.val⁻¹∈centralizer (standardThree E:Set G) := by
    rw [←hgroup]
    apply Subgroup.mem_centralizer_iff.mpr
    rintro z ⟨u,hu,rfl⟩
    have hucomm := (Subgroup.mem_centralizer_iff.mp hcU) u hu
    change (MulAut.conj n.val) u*(MulAut.conj n.val) c=
      (MulAut.conj n.val) c*(MulAut.conj n.val) u
    rw [←map_mul,←map_mul,hucomm]
  have hm := M.mul_mem (M.mul_mem (M.inv_mem hnM) (hc hh)) hnM
  simpa only [mul_assoc,inv_mul_cancel_left,inv_mul_cancel,mul_one] using hm

theorem natural_source_standard_three_escape_of_normal_layer
    (h : ChapterE.Section06.HypothesisE61 K₀ T M V)
    (L : Subgroup (Automizer V)) [L.Normal]
    (e : L≃*Atlas.G2.Natural.BinaryNormalizer.Derived)
    (E₀ : Additive V≃ₗ[ZMod 2]Atlas.G2.Natural.Space K)
    (hE₀ : ∀(l:L) v,E₀ (automizerRepresentation V l v)=
      Atlas.G2.Natural.derivedAction K (e l) (E₀ v))
    (hFour : ∀l : Subgroup G,l≤V → Nat.card l=4 →
      ((markedForm (E₀.trans (Atlas.G2.Restricted.NaturalCoordinates.equiv K))).restrict
        (ambientSpace (V:=V) l)).Nondegenerate → centralizer (l:Set G)≤M)
    (hact : ∀U∈ChapterE.Section06.obstructionFamily M V,
      (∀X : Subgroup G,U<X→X≤V→centralizer (X:Set G)≤M)→
      1<subgroupCorank V U→∃x∈M⊓centralizer (U:Set G),x∉centralizer (V:Set G))
    (hr : globalR V=3) :
    ¬centralizer (standardThree (E₀.trans (Atlas.G2.Restricted.NaturalCoordinates.equiv K)):Set G)≤M := by
  obtain ⟨f,hf,hres,hfull⟩ := Atlas.G2.Natural.BinaryNormalizer.ambient_embedding
    (automizerRepresentation V) L e E₀ hE₀ (automizerRepresentation_injective V)
  let E := E₀.trans (Atlas.G2.Restricted.NaturalCoordinates.equiv K)
  apply natural_source_standard_three_escape h E f hf _ _ hFour hact hr
  · intro a v
    change Atlas.G2.Restricted.NaturalCoordinates.equiv K
      (E₀ (automizerRepresentation V a v))=_
    rw [hfull]
    change Atlas.G2.Restricted.NaturalCoordinates.equiv K
      (Atlas.G2.Natural.action K (f a) (E₀ v))=
      Atlas.G2.Restricted.NaturalCoordinates.equiv K (Atlas.G2.Natural.action K (f a)
        ((Atlas.G2.Restricted.NaturalCoordinates.equiv K).symm
          (Atlas.G2.Restricted.NaturalCoordinates.equiv K (E₀ v))))
    rw [LinearEquiv.symm_apply_apply]
  · intro g
    refine ⟨(e.symm g).val,?_⟩
    rw [hres,e.apply_symm_apply]

end CFSG.Quasithin.Chapter13.Section03.UnitaryGeometry
