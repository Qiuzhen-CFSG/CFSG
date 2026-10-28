module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.LocalStructure
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Incidence.SourceContext
public import Theory.SpecificGroups.PSL3Two.Parabolics.LineCore

/-!
# Local residual generation by the opposite two-core

In the point parabolic of SL₃(2), two elements of the opposite radical,
and their conjugates by the local reflection, generate the upper triangular
subgroup and the reflection. The binary Bruhat decomposition then gives the
whole point parabolic. The diagram involution supplies the line case, and
simultaneous conjugation supplies every marked flag.

Normal closures commute with the actual restricted quotient projection.
Consequently the local normal closure of the opposite core covers the model
parabolic and contains Q = O₂(E). Its index in the actual local normalizer
divides |E:Q|, so it contains O^{2′}(Mᵢ). All normality in this argument is
relative to Mᵢ; neither E = Q nor Mᵢ = Pᵢ is assumed.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), extension clause (A) on p.828, local notation on pp.829,832, and
the final paragraph of (1.7)(ii) on p.848. This supplies the group-theoretic
`residual_generation` field of the literal dual pencil.
-/

public section

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.RankOnePairing.Incidence.DualGeometry
open Subgroup
variable {G H : Type*} [Group G] [Group H]
private theorem localGenerated_map (P X : Subgroup G) (hX : X ≤ P) (f : G →* H) :
    (localGenerated P X).map f = localGenerated (P.map f) (X.map f) := by
  have hx : (X.subgroupOf P).map (f.subgroupMap P) =
      (X.map f).subgroupOf (P.map f) := by
    apply map_injective (P.map f).subtype_injective
    rw [map_map, map_subgroupOf_eq_of_le (map_mono hX)]
    change (X.subgroupOf P).map (f.comp P.subtype) = _
    rw [← map_map, map_subgroupOf_eq_of_le hX]
  calc
    _ = ((normalClosure (X.subgroupOf P : Set P)).map (f.subgroupMap P)).map
        (P.map f).subtype := by rw [localGenerated, map_map, map_map]; rfl
    _ = _ := by rw [map_normalClosure _ _ (f.subgroupMap_surjective P), ← coe_map, hx]; rfl

open Matrix.PSL3Two hiding SL
open Matrix.PSL3Two.Bruhat
private def upperWords : Fin 8 → List (Fin 3) :=
  ![[], [0], [1], [0,1], [2], [0,1,2], [1,2], [0,2]]
private theorem upper_words : ∀ i : Fin 8,
    ((upperWords i).map (![upper 1, upper 2, upper 4])).prod = upper i := by decide +kernel

private theorem point_generation (N : Subgroup SL)
    (hR : lineParabolicSL.pCoreIn 2 ≤ N)
    (hn : pointParabolicSL ≤ normalizer (N : Set SL)) : pointParabolicSL ≤ N := by
  have h2 : upper 2 ∈ N := by
    apply hR
    rw [lineParabolicSL_pCoreIn_two_eq_R]
    exact ⟨Multiplicative.ofAdd (1,0), rfl⟩
  have h4 : upper 4 ∈ N := by
    apply hR
    rw [lineParabolicSL_pCoreIn_two_eq_R]
    exact ⟨Multiplicative.ofAdd (0,1), rfl⟩
  have hs : perm 1 ∈ pointParabolicSL := by decide +kernel
  have h1 : upper 1 ∈ N := by
    have he : perm 1 * upper 2 * (perm 1)⁻¹ = upper 1 := by decide +kernel
    rw [← he]
    exact le_normalizer_iff.mp hn _ hs _ h2
  have hp : perm 1 ∈ N := by
    have he : upper 4 * (perm 1 * upper 4 * (perm 1)⁻¹) * upper 4 = perm 1 := by decide +kernel
    rw [← he]
    exact N.mul_mem (N.mul_mem h4 (le_normalizer_iff.mp hn _ hs _ h4)) h4
  have hu (i : Fin 8) : upper i ∈ N := by
    rw [← upper_words]
    apply N.list_prod_mem
    intro x hx
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
    fin_cases j
    · exact h1
    · exact h2
    · exact h4
  intro x hx
  obtain ⟨a,b,c,rfl⟩ := decomposition x
  have hb : perm b ∈ pointParabolicSL := by
    exact (pointParabolicSL.mul_mem_cancel_left (upper_mem a).1).mp
      ((pointParabolicSL.mul_mem_cancel_right (upper_mem c).1).mp hx)
  have hb' : b = 0 ∨ b = 1 := by
    have ht : ∀ j : Fin 6, perm j ∈ pointParabolicSL → j = 0 ∨ j = 1 := by decide +kernel
    exact ht b hb
  apply N.mul_mem (N.mul_mem (hu a) _) (hu c)
  rcases hb' with rfl | rfl
  · have he : perm 0 = 1 := by decide +kernel
    rw [he]
    exact N.one_mem
  · exact hp

private theorem localGenerated_normalizes (P X : Subgroup G) :
    P ≤ normalizer (localGenerated P X : Set G) := by
  apply (normal_subgroupOf_iff_le_normalizer (map_subtype_le _)).mp
  change (((normalClosure (X.subgroupOf P : Set P)).map P.subtype).comap P.subtype).Normal
  rw [comap_map_eq_self_of_injective P.subtype_injective]
  infer_instance

private theorem point_localGenerated :
    localGenerated pointParabolicSL (lineParabolicSL.pCoreIn 2) = pointParabolicSL := by
  apply le_antisymm (map_subtype_le _)
  apply point_generation
  · apply le_localGenerated
    rw [lineParabolicSL_pCoreIn_two_eq_R]
    rintro x ⟨a, rfl⟩
    rw [mem_pointParabolicSL_iff]
    exact ⟨rfl, rfl⟩
  · exact localGenerated_normalizes _ _

private theorem line_map_diagram : lineParabolicSL.map MarkedAutomorphisms.diagram.toMonoidHom =
    pointParabolicSL := by
  apply map_injective (f := MarkedAutomorphisms.diagram.toMonoidHom) MarkedAutomorphisms.diagram.injective
  rw [MarkedAutomorphisms.pointParabolic_map_diagram, map_map]
  have he : MarkedAutomorphisms.diagram.toMonoidHom.comp
      MarkedAutomorphisms.diagram.toMonoidHom = MonoidHom.id SL := by
    apply MonoidHom.ext
    intro x
    exact MarkedAutomorphisms.diagram_involutive x
  rw [he, map_id]

private theorem line_localGenerated :
    localGenerated lineParabolicSL (pointParabolicSL.pCoreIn 2) = lineParabolicSL := by
  have h := congrArg (fun K : Subgroup SL => K.map MarkedAutomorphisms.diagram.toMonoidHom)
    point_localGenerated
  have hle : lineParabolicSL.pCoreIn 2 ≤ pointParabolicSL := by
    rw [lineParabolicSL_pCoreIn_two_eq_R]
    rintro x ⟨a, rfl⟩
    exact (mem_pointParabolicSL_iff _).mpr ⟨rfl, rfl⟩
  rw [localGenerated_map _ _ hle, MarkedAutomorphisms.pointParabolic_map_diagram,
    map_pCoreIn_of_injective 2 _ _ MarkedAutomorphisms.diagram.injective,
    line_map_diagram] at h
  exact h

private theorem model_localGenerated (g : SL) (i : Bool) :
    localGenerated (modelParabolic g i) ((modelParabolic g (!i)).pCoreIn 2) =
      modelParabolic g i := by
  have hp : lineParabolicSL.pCoreIn 2 ≤ pointParabolicSL := by
    rw [lineParabolicSL_pCoreIn_two_eq_R]
    rintro x ⟨a, rfl⟩
    exact (mem_pointParabolicSL_iff _).mpr ⟨rfl, rfl⟩
  have hl : pointParabolicSL.pCoreIn 2 ≤ lineParabolicSL := by
    have h := map_mono (f := MarkedAutomorphisms.diagram.toMonoidHom) hp
    rwa [map_pCoreIn_of_injective 2 _ _ MarkedAutomorphisms.diagram.injective,
      line_map_diagram, MarkedAutomorphisms.pointParabolic_map_diagram] at h
  cases i
  · have h := congrArg (fun K : Subgroup SL => K.map (MulAut.conj g).toMonoidHom)
      point_localGenerated
    rwa [localGenerated_map _ _ hp, map_pCoreIn_of_injective 2 _ _ (MulAut.conj g).injective] at h
  · have h := congrArg (fun K : Subgroup SL => K.map (MulAut.conj g).toMonoidHom)
      line_localGenerated
    rwa [localGenerated_map _ _ hl, map_pCoreIn_of_injective 2 _ _ (MulAut.conj g).injective] at h

private theorem residual_le_of_image (P X Q : Subgroup G) (f : G →* H)
    (hX : X ≤ P) (hQX : Q ≤ X) (hQker : Q ≤ f.ker)
    (hodd : Nat.Coprime 2 (Q.relIndex f.ker))
    (himage : (localGenerated P X).map f = P.map f) :
    localResidual P ≤ localGenerated P X := by
  let N : Subgroup P := normalClosure (X.subgroupOf P : Set P)
  let K : Subgroup P := f.ker.subgroupOf P
  let q : P →* H := f.comp P.subtype
  have hs : N ⊔ K = ⊤ := by
    have hm : N.map q = (⊤ : Subgroup P).map q := by
      change N.map (f.comp P.subtype) = _
      rw [← map_map]
      change (localGenerated P X).map f = _
      rw [himage, ← MonoidHom.range_eq_map]
      change P.map f = (f.comp P.subtype).range
      rw [MonoidHom.range_comp, P.range_subtype]
    have hc := congrArg (fun U : Subgroup H => U.comap q) hm
    have hk : q.ker = K := rfl
    simpa only [comap_map_eq, top_sup_eq, hk] using hc
  have hQN : Q.subgroupOf P ≤ N := by
    intro x hx
    exact le_normalClosure (hQX hx)
  have hidx : N.index ∣ Q.relIndex f.ker := by
    have h1 : N.relIndex K ∣ (Q.subgroupOf P).relIndex K := relIndex_dvd_of_le_left K hQN
    have he : (Q.subgroupOf P).relIndex K = Q.relIndex (P ⊓ f.ker) := by
      rw [← relIndex_subgroupOf (H := Q) (show P ⊓ f.ker ≤ P from inf_le_left),
        inf_subgroupOf_left]
    rw [← relIndex_sup_left K N, hs, relIndex_top_right, he] at h1
    have h2 : Q.relIndex (P ⊓ f.ker) ∣ Q.relIndex f.ker := by
      exact dvd_of_mul_right_eq ((P ⊓ f.ker).relIndex f.ker)
        (relIndex_mul_relIndex Q (P ⊓ f.ker) f.ker
          (le_inf (hQX.trans hX) hQker) inf_le_right)
    exact h1.trans h2
  exact map_mono (primeToResidual_le N (hodd.coprime_dvd_right hidx))

variable {M : Type*} [Group M]

/-- The untilded local residual is generated inside the actual local normalizer
by conjugates of the opposite local two-core. This uses only the published
local facts and the odd index of the extension kernel's two-core. -/
theorem residual_generation {e : Extension (M := M)} {Z : Subgroup M}
    (f : LocalFacts e Z) (i : Bool) :
    localResidual (localParabolic e i) ≤
      localGenerated (localParabolic e i) (localCore (localParabolic e (!i))) := by
  have hX : localCore (localParabolic e (!i)) ≤ localParabolic e i := by
    rw [f.core_eq]
    exact (show selectedCore e (!i) ≤ commonSylow e from inf_le_left).trans
      (commonSylow_le_localParabolic e i)
  have hQX : extensionCore e.projection ≤ localCore (localParabolic e (!i)) := by
    exact le_pCoreIn_of_normalizes (extensionCore_isPGroup _) (f.core_le (!i))
      (by rw [normalizer_eq_top]; exact le_top)
  apply residual_le_of_image _ _ (extensionCore e.projection) e.projection hX hQX
    (extensionCore_le_kernel _)
  · have he : (extensionCore e.projection).subgroupOf e.projection.ker =
        pCore 2 e.projection.ker := comap_map_eq_self_of_injective e.projection.ker.subtype_injective _
    change Nat.Coprime 2 ((extensionCore e.projection).subgroupOf e.projection.ker).index
    rw [he]
    exact e.base.odd_index
  · rw [localGenerated_map _ _ hX, f.parabolic_image, f.core_image]
    exact model_localGenerated e.flag i
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.RankOnePairing.Incidence.DualGeometry
