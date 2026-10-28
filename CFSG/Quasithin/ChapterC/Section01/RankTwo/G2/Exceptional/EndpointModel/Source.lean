module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.G2.Exceptional.OmegaOrbit
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.G2.Exceptional.Comparison.LocalSource

/-!
Adapted from the checked Chapter15 MarkedMS.G2Reconstruction proof to the
exceptional MS2(b) input. Only the two-group and core-containment consequences
of MS2 are used; the original SmallMSPair interface is unchanged.

# The literal full G₂ natural quotient at a critical endpoint

Conjugate original-group coordinates identify each original-color seed
with the entire omega orbit. Transport its natural projection and ambient
actor to the actual amalgam subgroups. Injectivity of the original-group
embedding retains the exact core kernel, residual image, and residual
centralizer kernel, together with the literal conjugation equation.

The resulting model discharges `Comparison.EndpointModelInput`; the
critical-image placement and critical-distance proofs remain separate.
Source: AS C.1.31–32; MS93 (3.2)(vii), (3.3), pp.863–868.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.G2Exceptional.Reconstruction
open ChapterB.QuasisimpleSource ChapterC ChapterC.BinaryMS.MS93 MSCentralOrbit

private theorem vertex_seed_coordinates {M : Type*} [Group M] [Finite M]
    (T : Subgroup M) (hp : IsPGroup 2 T) (hQT : pCore 2 M ≤ T)
    {z : Vertex T} (hz : color T z = false) :
    ∃ i : M →* FreeAmalgam T, Function.Injective i ∧
      i.range = stabilizer T z ∧ (pResidual 2 M).map i = Ltilde T z ∧
      (omegaOrbit T).map i = Z T z ∧ (pCore 2 M).map i = Q T z := by
  obtain ⟨g,rfl⟩ := exists_mVertex_of_color T hz
  let i := (MulAut.conj g⁻¹).toMonoidHom.comp (embedM T)
  refine ⟨i,(MulAut.conj g⁻¹).injective.comp (embedM_injective T),?_,?_,?_,?_⟩
  · have hh := stabilizer_act T g (alpha T)
    dsimp only [i]
    rw [MonoidHom.range_comp]
    change (Mbar T).map (MulAut.conj g⁻¹).toMonoidHom = _
    simpa only [alpha,act_mVertex,one_mul,stabilizer_m_base] using hh.symm
  · have hh := Ltilde_act T g (alpha T)
    rw [Ltilde_alpha] at hh
    simpa only [alpha,act_mVertex,one_mul,map_map] using hh.symm
  · have hh := Z_act T g (alpha T)
    rw [Z_alpha_eq_omegaOrbit] at hh
    simpa only [alpha,act_mVertex,one_mul,map_map] using hh.symm
  · have hh := Q_act T g (alpha T)
    rw [Q_alpha T hp hQT] at hh
    simpa only [alpha,act_mVertex,one_mul,map_map] using hh.symm

private theorem endpointModel_of_coordinates {M : Type*} [Group M] [Finite M]
    (T : Subgroup M) (hp : IsPGroup 2 T) (hQT : pCore 2 M ≤ T)
    (a : M →* Atlas.G2.Model (ZMod 2)) (ha : a.ker = pCore 2 M)
    (haL : (pResidual 2 M).map a = commutator (Atlas.G2.Model (ZMod 2)))
    (π : omegaOrbit T →* Multiplicative Comparison.NaturalSpace)
    (hπs : Function.Surjective π)
    (hπk : π.ker.map (omegaOrbit T).subtype =
      omegaOrbit T ⊓ centralizer (pResidual 2 M : Set M))
    (hπ : ∀ (g : M) (v : omegaOrbit T),
      π ⟨g * v.val * g⁻¹, Subgroup.Normal.conj_mem inferInstance _ v.property g⟩ =
      Multiplicative.ofAdd (Atlas.G2.Restricted.NaturalCoordinates.action (ZMod 2)
        (a g) (π v).toAdd))
    {z : Vertex T} (hz : color T z = false) : Nonempty (Comparison.EndpointModel T z) := by
  obtain ⟨i,hi,hir,hiL,hiZ,hiQ⟩ := vertex_seed_coordinates T hp hQT hz
  let d : M ≃* stabilizer T z :=
    (MonoidHom.ofInjective hi).trans (MulEquiv.subgroupCongr hir)
  have hd (g : stabilizer T z) : i (d.symm g) = g.val :=
    congrArg Subtype.val (d.apply_symm_apply g)
  let j : omegaOrbit T →* Z T z :=
    (i.comp (omegaOrbit T).subtype).codRestrict _ (fun v => hiZ ▸ mem_map_of_mem i v.property)
  have hj : Function.Bijective j := by
    constructor
    · intro v w h
      exact Subtype.ext (hi (congrArg Subtype.val h))
    · intro v
      have hv : v.val ∈ (omegaOrbit T).map i := hiZ.symm ▸ v.property
      obtain ⟨w,hw,he⟩ := hv
      exact ⟨⟨w,hw⟩,Subtype.ext he⟩
  let f : omegaOrbit T ≃* Z T z := MulEquiv.ofBijective j hj
  have hf (v : omegaOrbit T) : (f v).val = i v.val := rfl
  have hfi (v : Z T z) : i (f.symm v).val = v.val := by
    rw [←hf,f.apply_symm_apply]
  let κ := ElementaryMovedCover.embeddedQuotient a i hi (stabilizer T z) hir
  let π' := π.comp f.symm.toMonoidHom
  refine ⟨{
    projection := π'
    projection_surjective := hπs.comp f.symm.surjective
    actor := κ
    actor_kernel := ?_
    actor_residual := ?_
    projection_kernel := ?_
    intertwines := ?_ }⟩
  · rw [ElementaryMovedCover.embeddedQuotient_kernel,ha]
    exact hiQ
  · rw [←hiL,ElementaryMovedCover.embeddedQuotient_subgroup,haL]
  · ext v
    constructor
    · rintro ⟨w,hw,rfl⟩
      have hw' : (f.symm w).val ∈ π.ker.map (omegaOrbit T).subtype :=
        ⟨f.symm w,hw,rfl⟩
      rw [hπk] at hw'
      refine ⟨w.property,?_⟩
      intro g hg
      rw [←hiL] at hg
      obtain ⟨b,hb,rfl⟩ := hg
      have hc := congrArg i (hw'.2 b hb)
      simpa only [map_mul,hfi,Subgroup.coe_subtype] using hc
    · rintro ⟨hv,hc⟩
      let w : Z T z := ⟨v,hv⟩
      have hw' : (f.symm w).val ∈ π.ker.map (omegaOrbit T).subtype := by
        rw [hπk]
        refine ⟨(f.symm w).property,?_⟩
        intro b hb
        apply hi
        have hc' := hc (i b) (hiL ▸ mem_map_of_mem i hb)
        simpa only [map_mul,hfi] using hc'
      obtain ⟨u,hu,he⟩ := hw'
      have he' : u = f.symm w := Subtype.ext he
      refine ⟨w,?_,rfl⟩
      change π (f.symm w) = 1
      rwa [←he']
  · intro g v
    change π (f.symm _) = Multiplicative.ofAdd
      (Atlas.G2.Restricted.NaturalCoordinates.action (ZMod 2) (a (d.symm g))
        (π (f.symm v)).toAdd)
    rw [←hπ (d.symm g) (f.symm v)]
    congr 1
    apply f.injective
    rw [f.apply_symm_apply]
    apply Subtype.ext
    rw [hf,map_mul,map_mul,map_inv,hd,hfi]

universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
local notation "H" => (L ⊔ R : Subgroup G)
local notation "T" => R.subgroupOf (L ⊔ R)

/-- Every original-color endpoint has the entire seed's marked natural quotient. -/
theorem endpointModel_knownSimple (h : Pair KnownSimple.IsKnownSimple L R)
    (e : (L ⧸ pCore 2 L) ≃* commutator (Atlas.G2.Model (ZMod 2)))
    {z : Vertex T} (hz : color T z = false) : Nonempty (Comparison.EndpointModel T z) := by
  obtain ⟨a,ha,haL,π,hπs,hπk,hπ⟩ := omegaOrbit_natural_coordinates h e
  rw [←relative_residual h] at haL hπk
  exact endpointModel_of_coordinates T (edge_two_group h) (core_le_edge h)
    a ha haL π hπs hπk hπ hz

/-- Discharges the literal endpoint-model premise of the critical comparison. -/
theorem endpointModelInput_knownSimple : Comparison.EndpointModelInput.{u} := by
  intro J _ _ L R h e _ z hc
  exact endpointModel_knownSimple h e
    (critical_endpoint_color _ _ rfl _ hc)

end CFSG.Quasithin.ChapterC.G2Exceptional.Reconstruction
