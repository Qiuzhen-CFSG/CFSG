module
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.PairedFactorOrbit.OrbitAssembly
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.PairedFactorOrbit.Coordinates
public import Theory.GroupTheory.PResidual.PerfectCover
/-!
# The two original B.6.10 factor orbits

Keep the same B.5.6 source pair, natural marking, centralizer quotient and
chosen original Sylow exchange. The marked axis and prescribed Sylow
coordinates discharge every input to the per-factor orbit calculation.
The original Baumann subgroup normalizes each mapped residual, is Sylow
in its join with that residual, and its original alpha orbit is precisely
[U,Kᵢ] C_alpha(Kᵢ). No whole-module splitting, per-factor action conclusion,
or local minimal-parabolic/Frattini assertion is assumed.

The actual C.1.26/C.1.28 consumer selects its local component separately.
Source: Aschbacher–Smith B.6.10 and E.2.3(2), pp.117 and216–217.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
set_option backward.isDefEq.respectTransparency false
namespace CFSG.Quasithin.ChapterB.RankOneBaumann.PairedFactorOrbit
open QuasisimpleSource SourceInduction
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
theorem source_first_orbit
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (d : SourceTwoFactorCase ((NormalElementaryQuotient.representation U q hq hker).comp
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)).subtype))
    (F : BinaryField) (c : d.MarkedProduct (linearNatural F 2))
    (hexchange : letI := offenderSubgroup_normal (NormalElementaryQuotient.representation U q hq hker)
      ∃ t : T.mapSurjective hq,
        d.first.map (MulAut.conjNormal (t:H)).toMonoidHom = d.second ∧
        d.second.map (MulAut.conjNormal (t:H)).toMonoidHom = d.first) :
    let Y := offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)
    let K := factorResidual q Y d.first
    conjugateSpanBy (thompsonAlpha (T : Subgroup G)) K =
      (⁅U,K⁆ : Subgroup G) ⊔ (thompsonAlpha (T : Subgroup G) ⊓ centralizer (K : Set G)) := by
  let α := NormalElementaryQuotient.representation U q hq hker
  let Y := offenderSubgroup α
  let K := factorResidual q Y d.first
  let D := Matrix.SpecialLinearGroup (Fin 2) F.Carrier
  let j : D →* H := Y.subtype.comp (c.action.groupEquiv.symm.toMonoidHom.comp (MonoidHom.inl D D))
  let := offenderSubgroup_normal α
  obtain ⟨ρ,hρ,hnat,he,⟨hJq,hBq⟩,hfix⟩ := source_images_and_fixedSpace T hP U hU hJ q hq hker d F c hexchange
  obtain ⟨P₀,hP₀⟩ := (T.mapSurjective hq).exists_sylow_map_eq_inf_of_normal Y
  have hPJ : (P₀ : Subgroup Y).map Y.subtype = (elementaryAbelianMaxJ (T : Subgroup G)).map q :=
    hP₀.trans hJq.symm
  obtain ⟨P,Q,hPQ⟩ := layer_fixedSpace_product F Y c.action.groupEquiv ρ hnat _ P₀ hPJ
  have hKI : K.map q = (pResidual 2 D).map j :=
    first_residual_image_of_marking F q hq Y d.first c.action.groupEquiv c.first_eq
  have hK : IsPPerfect 2 K := isPPerfect_embedded_pResidual 2 (factorPreimage q Y d.first)
  have hact : ∀ g v, c.quotientMap (α (j g) v) =
      (linearNatural F 2 g (c.quotientMap v).1,(c.quotientMap v).2) := by
    intro g v
    have hh := c.quotientMap_action (c.action.groupEquiv.symm (g,1)) v
    rw [c.action.groupEquiv.apply_symm_apply] at hh
    change c.quotientMap (α (j g) v) =
      (linearNatural F 2 g (c.quotientMap v).1,linearNatural F 2 1 (c.quotientMap v).2) at hh
    simpa only [map_one,Module.End.one_apply] using hh
  have hk : c.quotientMap.ker ≤ fixedSpace α (K.map q) := by
    rw [c.quotientMap_ker]
    intro v hv a
    obtain ⟨g,hg,hga⟩ := hKI.le a.property
    have hY : (a:H) ∈ Y := by
      rw [←hga]
      exact (c.action.groupEquiv.symm (g,1)).property
    exact hv ⟨a,hY⟩
  apply first_factor_orbit_of_coordinates F U q hq hker
    (elementaryAbelianMaxJ (T : Subgroup G)) (thompsonAlpha (T : Subgroup G))
    (pResidual 2 G) K (factorResidual_le_residual q Y d.first) hK
    (source_global_baumann_and_alpha T hP U hU hJ q hq hker d F c hexchange).2
    c.quotientMap c.quotientMap_surjective j hKI hact hk P Q
  rw [hfix,hPQ]
theorem source_factor_conclusions
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (d : SourceTwoFactorCase ((NormalElementaryQuotient.representation U q hq hker).comp
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)).subtype))
    (F : BinaryField) (c : d.MarkedProduct (linearNatural F 2))
    (hexchange : letI := offenderSubgroup_normal (NormalElementaryQuotient.representation U q hq hker)
      ∃ t : T.mapSurjective hq,
        d.first.map (MulAut.conjNormal (t:H)).toMonoidHom = d.second ∧
        d.second.map (MulAut.conjNormal (t:H)).toMonoidHom = d.first) :
    let Y := offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)
    let B := baumann (T : Subgroup G)
    let E := thompsonAlpha (T : Subgroup G)
    let K₁ := factorResidual q Y d.first
    let K₂ := factorResidual q Y d.second
    Chapter1.IsSylowIn 2 B (pResidual 2 G ⊔ B) ∧
      (B ≤ normalizer (K₁ : Set G) ∧ Chapter1.IsSylowIn 2 B (K₁ ⊔ B) ∧
        conjugateSpanBy E K₁ = (⁅U,K₁⁆ : Subgroup G) ⊔ (E ⊓ centralizer (K₁ : Set G))) ∧
      (B ≤ normalizer (K₂ : Set G) ∧ Chapter1.IsSylowIn 2 B (K₂ ⊔ B) ∧
        conjugateSpanBy E K₂ = (⁅U,K₂⁆ : Subgroup G) ⊔ (E ⊓ centralizer (K₂ : Set G))) := by
  obtain ⟨hS,h₁,h₂⟩ := source_residual_normalizers_and_sylows T hP U hU hJ q hq hker d F c hexchange
  refine ⟨hS,⟨h₁.1,h₁.2,source_first_orbit T hP U hU hJ q hq hker d F c hexchange⟩,h₂.1,h₂.2,?_⟩
  apply source_first_orbit T hP U hU hJ q hq hker (sourceSwap d) F (markedSwap c)
  let := offenderSubgroup_normal (NormalElementaryQuotient.representation U q hq hker)
  obtain ⟨t,ht₁,ht₂⟩ := hexchange
  exact ⟨t,ht₂,ht₁⟩
end CFSG.Quasithin.ChapterB.RankOneBaumann.PairedFactorOrbit
