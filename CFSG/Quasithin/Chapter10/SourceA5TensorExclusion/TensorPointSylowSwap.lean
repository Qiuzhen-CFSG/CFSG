module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorThompsonActor
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorPointSylowTransport
public import Theory.Representation.OrthogonalFourPlusMatrix.LowRankNonsingularConjugate
public import Theory.Representation.OrthogonalFourPlusMatrix.InvolutionResidual.Defs
public import Theory.Representation.OrthogonalFourPlusMatrix.RankTwoFactorSwap

/-!
# A component-swapping element in the original point Sylow

In the generation-one branch, the moving Thompson family supplies an element
of the original Sylow group whose binary tensor action is an involution of
rank two. Its nonsingular displacement line is fixed pointwise over F₄.
Scaling a fixed vector to the prescribed determinant and lifting an inner
matrix conjugation places the cyclic two-subgroup in the actual point
centralizer. Sylow conjugacy there then places it in the literal C_T(v).

Both conjugations preserve the action's order and rank. Such a binary
rank-two involution does not normalize the marked first tensor factor,
which is exactly the image of the original component L. The resulting
point-Sylow element therefore lies outside N_G(L).

Source: Aschbacher–Smith 9.1.2(4), 9.2.4(2), and the point-Sylow argument
in 9.4.1, combined manuscript of 1 March 2004, printed pp.729–730,735–736.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation
open Representation.BinaryOffender.NaturalTensor
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ChapterE ClassicalOrthogonal.FourPlusMatrix
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

/-- The original component has the marked first-factor image. -/
theorem maximalAction_firstFactor_image :
    (L.subgroupOf D.maximalLocal).map m.maximalAction =
      Binary.InvolutionResidual.leftFactor := by
  have hLM : L ≤ D.maximalLocal :=
    (le_componentOrbit L T).trans (localOrbit T L).le_normalizer
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    let l : L := ⟨x,hx⟩
    refine ⟨m.firstMarking (e (QuotientGroup.mk' (pCore 2 L) l)),?_⟩
    change Binary.linearAction (_,1) = m.maximalAction x
    have hh := m.maximalAction_on_orbit ⟨l,le_componentOrbit L T l.property⟩
    rw [m.first_factor l] at hh
    exact hh.symm
  · rintro _ ⟨a,rfl⟩
    obtain ⟨l,hl⟩ := (m.firstMarking.surjective.comp
      (e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L)))) a
    change m.firstMarking (e (QuotientGroup.mk' (pCore 2 L) l)) = a at hl
    refine ⟨⟨l,hLM l.property⟩,l.property,?_⟩
    change m.maximalAction ⟨l,hLM l.property⟩ = Binary.linearAction (a,1)
    have hh := m.maximalAction_on_orbit ⟨l,le_componentOrbit L T l.property⟩
    rw [m.first_factor l,hl] at hh
    exact hh

/-- A maximal-local element normalizing L normalizes its actual matrix image. -/
theorem maximalAction_normalizes_firstFactor (t : D.maximalLocal)
    (ht : (t : G) ∈ normalizer (L : Set G)) :
    m.maximalAction t ∈ normalizer (Binary.InvolutionResidual.leftFactor :
      Set (Binary.V ≃ₗ[ZMod 2] Binary.V)) := by
  rw [←m.maximalAction_firstFactor_image]
  apply Subgroup.le_normalizer_map m.maximalAction
  apply mem_map_of_mem
  have hLM : L ≤ D.maximalLocal :=
    (le_componentOrbit L T).trans (localOrbit T L).le_normalizer
  rw [←subgroupOf_normalizer_eq hLM]
  exact ht

private theorem action_rank_conjugate (g t : D.maximalLocal) :
    operatorFixedCodim (m.maximalAction (g*t*g⁻¹)).toLinearMap =
      operatorFixedCodim (m.maximalAction t).toLinearMap := by
  simp only [map_mul,map_inv]
  exact BinaryNormalizerRank.rank_conj (m.maximalAction g) (m.maximalAction t)

private theorem action_square_conjugate (g t : D.maximalLocal)
    (ht : m.maximalAction t * m.maximalAction t = 1) :
    m.maximalAction (g*t*g⁻¹) * m.maximalAction (g*t*g⁻¹) = 1 := by
  simp only [map_mul,map_inv]
  calc
    _ = m.maximalAction g * (m.maximalAction t * m.maximalAction t) *
        (m.maximalAction g)⁻¹ := by group
    _ = 1 := by rw [ht,mul_one,mul_inv_cancel]

private theorem action_ne_one_of_rank_two (t : D.maximalLocal)
    (hr : operatorFixedCodim (m.maximalAction t).toLinearMap = 2) :
    m.maximalAction t ≠ 1 := by
  intro he
  rw [he] at hr
  change Module.finrank (ZMod 2)
    (LinearMap.range (LinearMap.id - LinearMap.id : Module.End (ZMod 2) Binary.V)) = 2 at hr
  rw [sub_self,LinearMap.range_zero,finrank_bot] at hr
  omega

/-- Place the given rank-two Sylow action in the prescribed point Sylow. -/
theorem exists_rank_two_point_action_of_rank_two_sylow_action
    (t : D.maximalLocal) (htT : (t : G) ∈ (T : Subgroup G))
    (ht1 : m.maximalAction t ≠ 1)
    (ht2 : m.maximalAction t * m.maximalAction t = 1)
    (htr : operatorFixedCodim (m.maximalAction t).toLinearMap = 2)
    (v : D.fullModule) (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G))
      (D.maximalLocal ⊓ centralizer ({(v : G)} : Set G))) :
    ∃ s : D.maximalLocal,
      (s : G) ∈ (T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G) ∧
      m.maximalAction s ≠ 1 ∧ m.maximalAction s * m.maximalAction s = 1 ∧
      operatorFixedCodim (m.maximalAction s).toLinearMap = 2 := by
  obtain ⟨a,ha⟩ := Binary.exists_inner_conjugate_fixing_nonsingular
    (m.maximalAction t) (m.maximalAction_mem_normalizer t) ht1 ht2 htr.le
    (m.sectionData.coordinates v).toAdd hv
  obtain ⟨l,hl⟩ := m.onto a
  let g : D.maximalLocal := ⟨l,(localOrbit T L).le_normalizer l.property⟩
  have hg : m.maximalAction g = Binary.linearAction a := by
    rw [m.maximalAction_on_orbit,hl]
  let b : D.maximalLocal := g * t * g⁻¹
  have hbfix : m.maximalAction b (m.sectionData.coordinates v).toAdd =
      (m.sectionData.coordinates v).toAdd := by
    dsimp only [b]
    rw [map_mul,map_mul,map_inv,hg]
    exact ha
  have hbC : (b : G) ∈ centralizer ({(v : G)} : Set G) := by
    rw [m.maximalAction_coordinates] at hbfix
    have he := congrArg (fun x : D.fullModule => (x : G))
      (m.coordinates_injective (Multiplicative.toAdd.injective hbfix))
    exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp he)
  have hb2 : m.maximalAction b * m.maximalAction b = 1 :=
    m.action_square_conjugate g t ht2
  have hbr : operatorFixedCodim (m.maximalAction b).toLinearMap = 2 :=
    (m.action_rank_conjugate g t).trans htr
  let Y := D.maximalLocal ⊓ centralizer ({(v : G)} : Set G)
  have hbY : (b : G) ∈ Y := ⟨b.property,hbC⟩
  have hbP : IsPGroup 2 (zpowers (b : G)) := by
    have hh := (T.isPGroup'.to_le (zpowers_le.mpr htT)).map
      (MulAut.conj (g : G)).toMonoidHom
    rw [MonoidHom.map_zpowers] at hh
    exact hh
  obtain ⟨P,hP⟩ := (hbP.comap_subtype :
    IsPGroup 2 ((zpowers (b : G)).subgroupOf Y)).exists_le_sylow
  obtain ⟨Q,hQ⟩ := hs
  obtain ⟨c,hc⟩ := MulAction.exists_smul_eq Y P Q
  let cM : D.maximalLocal := ⟨c,c.property.1⟩
  let s : D.maximalLocal := cM * b * cM⁻¹
  have hmem : MulAut.conj c (⟨b,hbY⟩ : Y) ∈ (Q : Subgroup Y) := by
    rw [←hc]
    exact mem_map_of_mem (MulAut.conj c).toMonoidHom (hP (mem_zpowers (b : G)))
  have hsTC : (s : G) ∈ (T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G) := by
    rw [←hQ]
    exact mem_map.mpr ⟨MulAut.conj c ⟨b,hbY⟩,hmem,rfl⟩
  have hsr : operatorFixedCodim (m.maximalAction s).toLinearMap = 2 :=
    (m.action_rank_conjugate cM b).trans hbr
  exact ⟨s,hsTC,m.action_ne_one_of_rank_two s hsr,
    m.action_square_conjugate cM b hb2,hsr⟩

/-- The original generation-one hypothesis supplies the point-Sylow action. -/
theorem exists_rank_two_point_action_of_generation_one
    (hout : Chapter3.HasMaximalOutside T D.maximalLocal)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hgen : generationParameter H = 1)
    (v : D.fullModule) (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G))
      (D.maximalLocal ⊓ centralizer ({(v : G)} : Set G))) :
    ∃ s : D.maximalLocal,
      (s : G) ∈ (T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G) ∧
      m.maximalAction s ≠ 1 ∧ m.maximalAction s * m.maximalAction s = 1 ∧
      operatorFixedCodim (m.maximalAction s).toLinearMap = 2 := by
  obtain ⟨t,htT,ht1,ht2,htr⟩ := m.exists_rank_two_sylow_action_of_generation_one hout hH hgen
  exact m.exists_rank_two_point_action_of_rank_two_sylow_action t htT ht1 ht2 htr v hv hs

/-- In the original generation-one branch, the specified point Sylow contains
an element that interchanges the marked tensor components. The involution
condition is required only of its action on the full module. -/
theorem exists_point_sylow_swap_of_generation_one
    (hout : Chapter3.HasMaximalOutside T D.maximalLocal)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hgen : generationParameter H = 1)
    (v : D.fullModule) (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G))
      (D.maximalLocal ⊓ centralizer ({(v : G)} : Set G))) :
    ∃ t : G, t ∈ (T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G) ∧
      t ∉ normalizer (L : Set G) := by
  obtain ⟨t,ht,_,ht2,htr⟩ :=
    m.exists_rank_two_point_action_of_generation_one hout hH hgen v hv hs
  refine ⟨t,ht,?_⟩
  intro hn
  exact Binary.rank_two_involution_not_normalize_leftFactor
    (m.maximalAction t) (m.maximalAction_mem_normalizer t)
    (by simpa only [pow_two] using ht2) htr
    (m.maximalAction_normalizes_firstFactor t hn)

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
