module
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.At.CentralizerBound.Components.HyperplaneMovement
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.At.CentralizerBound.Components.ConjugatorGeometry
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.At.CentralizerBound.Components.PlaneModels
public import Theory.SpecificGroups.PSL3Two.CubicNormalizer
public import Theory.GroupTheory.SylowCoprimeEquivalence
public import Theory.GroupTheory.SylowNormalizerCommutingFamily

/-!
# The actual conjugator in the ordinary-component branch of 12.4.8

This is the same-G,T version of the corresponding CentralizerBound proof.
Its configuration carries only Structural1222At at the original Sylow;
every subgroup, action and relative component map is unchanged.

Put the faithful cubic in a Sylow three-subgroup of L. Its image in
SL₃(2) has order three, and its normalizer contains an involution. The
Sylow normalizer lifting theorem gives l in L normalizing the original
cubic. Its square acts trivially on V. The B.4.8 displacement plane proves
that l moves U. Hence U intersect U^l is the required invariant plane,
and the same cubic acts faithfully on it. All conjugations are literal
left conjugations by this single chosen element.
Source: Aschbacher--Smith, Lemma 12.4.8, printed p.815.
-/
public section
open CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.Chapter12.Section04.SmallFusion
open CFSG.Quasithin.ChapterE
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.At.CentralizerBound
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V U : Subgroup G}

/-- Lift an involution of the marked cubic normalizer through O₂(L).
Its square fixes all of V, and it moves the original escaping hyperplane. -/
theorem Configuration.exists_component_conjugator (c : Configuration T L V U) :
    ∃ x l : G, x ∈ L ∧ orderOf x = 3 ∧ x ∈ normalizer (U : Set G) ∧
      x ∉ centralizer (U : Set G) ∧ l ∈ L ∧
      l ∈ normalizer (zpowers x : Set G) ∧ l ∉ normalizer (U : Set G) ∧
      l ^ 2 ∈ centralizer (V : Set G) := by
  obtain ⟨x,hxL,hx,hxN,hxU⟩ := c.exists_cubic_hyperplane_actor
  let a : L := ⟨x,hxL⟩
  have ha : orderOf a = 3 := (orderOf_coe a).symm.trans hx
  have haP : IsPGroup 3 (zpowers a) := IsPGroup.of_card (n := 1)
    (by simpa only [Nat.card_zpowers,pow_one] using ha)
  obtain ⟨P,hPa⟩ := haP.exists_le_sylow
  let q : L →* BinaryLinearThree.Group :=
    c.extension.quotientEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q :=
    c.extension.quotientEquiv.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : IsPGroup 2 q.ker := by
    change IsPGroup 2 (c.extension.quotientEquiv.toMonoidHom.comp
      (QuotientGroup.mk' (pCore 2 L))).ker
    rw [MonoidHom.ker_comp_of_injective _ _ c.extension.quotientEquiv.injective,
      QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hcop : Nat.Coprime 3 (Nat.card q.ker) := by
    obtain ⟨n,hn⟩ := hk.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  let Pbar := P.mapSurjective hq
  have hPbar : Nat.card Pbar = 3 := by
    rw [Pbar.card_eq_multiplicity, Matrix.PSL3Two.card_SL]
    decide +kernel
  have hP : Nat.card P = 3 :=
    (Nat.card_congr (P.equivOfSurjectiveCoprime q hq hcop Pbar).toEquiv).trans hPbar
  have heP : zpowers a = (P : Subgroup L) := eq_of_le_of_card_ge hPa
    (by rw [Nat.card_zpowers,ha,hP])
  obtain ⟨b,hb,hbN⟩ := BinaryLinearThree.exists_involution_normalizing_sylow_three Pbar
  have hnmap : (normalizer (P : Set L)).map q = normalizer (Pbar : Set BinaryLinearThree.Group) :=
    P.normalizer_map_surjective q hq
  obtain ⟨l,hlN,hlb⟩ := hnmap.symm ▸ hbN
  have hPl : (P : Subgroup L).map L.subtype = zpowers x := by
    rw [← heP,MonoidHom.map_zpowers]
    rfl
  have hlX : (l : G) ∈ normalizer (zpowers x : Set G) := by
    rw [← hPl]
    exact (P : Subgroup L).le_normalizer_map L.subtype (mem_map_of_mem _ hlN)
  have hlU : (l : G) ∉ normalizer (U : Set G) :=
    c.involution_moves_hyperplane l (by change orderOf (q l) = 2; rw [hlb]; exact hb)
  have hb2 : b ^ 2 = 1 := by simpa only [hb] using pow_orderOf_eq_one b
  have hq2 : q (l ^ 2) = 1 := by rw [map_pow,hlb,hb2]
  refine ⟨x,l,hxL,hx,hxN,hxU,l.property,hlX,hlU,?_⟩
  let _ := c.chosen.elementary
  intro v hv
  have he := c.extension.conjugation (l ^ 2) (Additive.ofMul ⟨v,hv⟩)
  change ((c.extension.action (q (l ^ 2)) (Additive.ofMul ⟨v,hv⟩)).toMul : G) =
    (l : G) ^ 2 * v * ((l : G) ^ 2)⁻¹ at he
  rw [hq2,map_one] at he
  exact (mul_inv_eq_iff_eq_mul.mp he.symm).symm

/-- The literal source plane, its faithful cubic, and the seed-layer placement
are constructed together from the original configuration and component. -/
theorem Configuration.exists_component_plane (c : Configuration T L V U)
    {K : Subgroup G} (hK : IsComponentIn K (centralizer (U : Set G))) :
    ∃ x l : G, x ∈ L ∧ orderOf x = 3 ∧ l ∈ L ∧
      l ∈ normalizer (zpowers x : Set G) ∧
      l ^ 2 ∈ normalizer (U : Set G) ∧
      l ^ 2 ∈ normalizer (U.map (MulAut.conj l).toMonoidHom : Set G) ∧
      let U₀ := U ⊓ U.map (MulAut.conj l).toMonoidHom
      U ⊔ U.map (MulAut.conj l).toMonoidHom = V ∧
        Nat.card U₀ = 4 ∧ subgroupCorank U U₀ = 1 ∧
        l ∈ normalizer (U₀ : Set G) ∧
        x ∈ normalizer (U₀ : Set G) ∧ x ∉ centralizer (U₀ : Set G) ∧
        IsSQTK KnownSimple.IsKnownSimple (centralizer (U₀ : Set G)) ∧
        K ≤ (componentLayer (centralizer (U₀ : Set G))).map
          (centralizer (U₀ : Set G)).subtype := by
  obtain ⟨x,l,hxL,hx,hxN,hxU,hl,hlX,hm,hsq⟩ := c.exists_component_conjugator
  have hsU : l ^ 2 ∈ normalizer (U : Set G) :=
    Subgroup.centralizer_le_normalizer _ ((centralizer_le c.le_module) hsq)
  have hWV : U.map (MulAut.conj l).toMonoidHom ≤ V :=
    (map_mono c.le_module).trans (mem_normalizer_iff_map_conj_eq.mp (c.chosen.normalizes hl)).le
  have hsW : l ^ 2 ∈ normalizer (U.map (MulAut.conj l).toMonoidHom : Set G) :=
    Subgroup.centralizer_le_normalizer _ ((centralizer_le hWV) hsq)
  have hg := c.conjugate_plane_geometry hl hm hsU
  have ha := c.cubic_on_conjugate_plane hl hm hsU hxL hxN hxU hlX
  have hKlayer := c.component_le_conjugate_plane_layer hK hl hm hsU
  exact ⟨x,l,hxL,hx,hl,hlX,hsU,hsW,hg.1,hg.2.1,hg.2.2.1,hg.2.2.2,ha.1,ha.2,hKlayer⟩

/-- The same actor proves the PSL₂ model for every actual containing component
of the constructed plane centralizer. No second plane is chosen. -/
theorem Configuration.plane_comparison_models (c : Configuration T L V U)
    {l x : G} (hl : l ∈ L) (hm : l ∉ normalizer (U : Set G))
    (hsq : l ^ 2 ∈ normalizer (U : Set G))
    (hxL : x ∈ L) (hx : orderOf x = 3) (hxN : x ∈ normalizer (U : Set G))
    (hxU : x ∉ centralizer (U : Set G))
    (hlX : l ∈ normalizer (zpowers x : Set G))
    {K₀ : Subgroup G}
    (hK₀ : IsComponentIn K₀
      (centralizer (U ⊓ U.map (MulAut.conj l).toMonoidHom : Set G))) :
    ∃ p, IsFermatOrMersennePrime p ∧ ClassicalGroup.IsPSL K₀ 2 p := by
  have hg := c.conjugate_plane_geometry hl hm hsq
  have ha := c.cubic_on_conjugate_plane hl hm hsq hxL hxN hxU hlX
  exact c.plane_component_fermatMersenne inf_le_left hg.2.2.1 hK₀ hx ha.1 ha.2
end CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.At.CentralizerBound
