module

public import Stellmacher.SectionTwo.OmegaNormalSupplement
public import Stellmacher.SectionTwo.CoreCentralizerSylow
public import Theory.GroupTheory.Commutator.CentralizerSylowSupplement

/-!
# The omega-supplement centralizer factorization in (2.3)

Let E be the normal closure of J(S), and W = Ω₁Z(J(S))V(S). Under the
Section Two hypotheses, the core equality and the noncentralizing case,
C_E(V(S)) lies in C_G(W)O₂(E). This is the containment needed to normalize
the intersection of the two conjugate omega-centers later in the proof.

The normal omega-supplement theorem makes W an elementary normal subgroup
of E, with [W,E] contained in V. In particular W centralizes V. Inside the
native group C_E(V), the action on W fixes both V and W/V. The central
commutator-layer theorem therefore expresses this centralizer as its kernel
on W joined with any Sylow 2-subgroup. The core-centralizer equality
identifies that Sylow image with O₂(E); two subtype maps transport the
result back to the original ambient group.

This formalizes the centralizer-factorization step of Stellmacher (2.3),
Journal of Algebra 190 (1997), p. 20. The source scan states that C_E(V)
centralizes W/V, not W itself as transcribed in the latex.
-/

namespace Stellmacher.SectionTwo

/-- The relative centralizer is contained in the omega-supplement centralizer times O₂(E). -/
public theorem two_three_omega_centralizer_factor
    {G : Type*} [Group G] [Finite G] (h : Hypotheses G) (S : Sylow 2 G)
    (hcore : pCore 2 G = (S : Subgroup G) ⊓ Subgroup.centralizer (vSubgroup S : Set G))
    (hnot : ¬ vSubgroup S ≤ Subgroup.centralizer
      (elementaryAbelianMaxJ (S : Subgroup G) : Set G)) :
    let E := Subgroup.normalClosure (elementaryAbelianMaxJ (S : Subgroup G) : Set G)
    let Z := omegaOneCenterAmbient (elementaryAbelianMaxJ (S : Subgroup G))
    let W := Z ⊔ vSubgroup S
    E ⊓ Subgroup.centralizer (vSubgroup S : Set G) ≤
      Subgroup.centralizer (W : Set G) ⊔ twoCoreAmbient E := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let V := vSubgroup S
  let J := elementaryAbelianMaxJ (S : Subgroup G)
  let E := Subgroup.normalClosure (J : Set G)
  let W := omegaOneCenterAmbient J ⊔ V
  let C := (Subgroup.centralizer (V : Set G)).subgroupOf E
  let U := W.subgroupOf E
  let R := V.subgroupOf E
  let Uc := U.subgroupOf C
  let Rc := R.subgroupOf C
  let f : C →* G := E.subtype.comp C.subtype
  have hf : Function.Injective f := E.subtype_injective.comp C.subtype_injective
  let _ : E.Normal := Subgroup.normalClosure_normal
  let _ : V.Normal := Subgroup.normalClosure_normal
  obtain ⟨hWe,hWE,hNW,hcomm,_⟩ := two_three_omega_normal_supplement h S hcore hnot
  let _ : IsElementaryAbelian 2 W := hWe
  let _ : IsElementaryAbelian 2 V := (vSubgroup_le_twoCore_and_elementaryAbelian h S).2
  have hVW : V ≤ W := le_sup_right
  have hVE : V ≤ E := hVW.trans hWE
  have hWC : W ≤ Subgroup.centralizer (V : Set G) := by
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact setLike_mul_comm (hVW hv) hw
  have hUC : U ≤ C := fun _ hw => hWC hw
  have hRC : R ≤ C := fun _ hv => hWC (hVW hv)
  let _ : U.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hWE).mpr hNW
  let _ : IsElementaryAbelian 2 R := IsElementaryAbelian.subgroupOf hVE
  let _ : IsElementaryAbelian 2 Rc := IsElementaryAbelian.subgroupOf hRC
  have hUmap : Uc.map f = W := by
    rw [← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hUC,
      Subgroup.map_subgroupOf_eq_of_le hWE]
  have hRmap : Rc.map f = V := by
    rw [← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hRC,
      Subgroup.map_subgroupOf_eq_of_le hVE]
  have htopmap : (⊤ : Subgroup C).map f ≤ E := by
    rintro _ ⟨c, _, rfl⟩
    exact c.val.property
  have hcommC : ⁅Uc, (⊤ : Subgroup C)⁆ ≤ Rc := by
    apply (Subgroup.map_le_map_iff_of_injective hf).mp
    rw [Subgroup.map_commutator, hUmap, hRmap]
    exact (Subgroup.commutator_mono le_rfl htopmap).trans hcomm
  have hVC : (⊤ : Subgroup C) ≤ Subgroup.centralizer (Rc : Set C) := by
    intro c _
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    apply hf
    change f r * f c = f c * f r
    exact (Subgroup.mem_centralizer_iff.mp c.property) (f r) hr
  obtain ⟨T,hT⟩ := twoCore_sylow_centralizer_of_core_equality S V E hcore
  have hfactor := Subgroup.centralizer_sup_sylow_eq_top_of_commutator_le Uc Rc T hVC hcommC
  have hTmap : (T : Subgroup C).map f = twoCoreAmbient E := by
    rw [← Subgroup.map_map, hT]
    rfl
  have hcent : (Subgroup.centralizer (Uc : Set C)).map f ≤
      Subgroup.centralizer (W : Set G) := by
    apply Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    rw [← hUmap, ← Subgroup.map_commutator]
    have hz : ⁅Subgroup.centralizer (Uc : Set C), Uc⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr le_rfl
    rw [hz, Subgroup.map_bot]
  have hfactorMap := congrArg (Subgroup.map f) hfactor
  rw [Subgroup.map_sup, hTmap] at hfactorMap
  change E ⊓ Subgroup.centralizer (V : Set G) ≤
    Subgroup.centralizer (W : Set G) ⊔ twoCoreAmbient E
  intro g hg
  have hgmap : g ∈ (⊤ : Subgroup C).map f :=
    ⟨⟨⟨g,hg.1⟩,hg.2⟩, Subgroup.mem_top _, rfl⟩
  rw [← hfactorMap] at hgmap
  exact (sup_le_sup hcent le_rfl) hgmap

end Stellmacher.SectionTwo
