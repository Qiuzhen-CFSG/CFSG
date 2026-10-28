module
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.Noncentrality.TwoRank
public import Theory.SpecificGroups.PSL3Two.FourMovingOuter

/-!
# The original actor is outer on both components

The source actor fixes the marked involution of each cubic module and sends
each module to its noncommuting conjugate. In the binary projective component,
an inner actor fixing that involution would preserve the four-group. Applying
this model fact to the two literal source components proves both outer actions.

Source: Aschbacher–Smith, Lemma 2.4.34, printed p.548, before replacing the
original actors by the paired model's commuting involutions.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter2.DoubleA3.Noncentrality
open Theory.GroupTheory
open ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
variable {d : MinimalBlockSetup M} {T : Sylow 2 G}

/-- Both original component actions are outer; the actor itself need not yet
be selected as an involution. -/
theorem source_x_outer
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (c : SourcePairCoordinates d T) (g : SourceCentralizerGeometry c)
    (K : Subgroup G) (hK : IsComponentIn K (centralizer ({g.z₂} : Set G)))
    (hE : K = (Theory.GroupTheory.componentLayer (centralizer ({g.z₂} : Set G))).map
      (centralizer ({g.z₂} : Set G)).subtype)
    (ho : pPrimeCore 2 (centralizer ({g.z₂} : Set G)) = ⊥)
    (hfirst : d.block.map d.H.subtype ≤ K)
    (hmodel : Nonempty (K ≃* alternatingGroup (Fin 6)) ∨ Nonempty (K ≃* Matrix.PSL3Two.PSL))
    (hcomm : c.U₂ ≤ centralizer (K : Set G)) :
    let Ks := K.map (MulAut.conj c.s⁻¹).toMonoidHom
    ∃ hxK : c.x ∈ normalizer (K : Set G), ∃ hxKs : c.x ∈ normalizer (Ks : Set G),
      K.normalizerMonoidHom ⟨c.x,hxK⟩ ∉ MulAut.innerSubgroup K ∧
      Ks.normalizerMonoidHom ⟨c.x,hxKs⟩ ∉ MulAut.innerSubgroup Ks := by
  let Ks := K.map (MulAut.conj c.s⁻¹).toMonoidHom
  obtain ⟨_,_,_,_,hxK,hxKs,hsK,_⟩ := source_commuting_components c g K hK hE ho hfirst hmodel hcomm
  obtain ⟨_,⟨eK⟩,_⟩ := source_pair_two_rank hG hu c g K hK hE ho hfirst hmodel hcomm
  let eS : K ≃* Ks := K.equivMapOfInjective (MulAut.conj c.s⁻¹).toMonoidHom
    (MulAut.conj c.s⁻¹).injective
  have hLs : c.L ≤ Ks := by
    change c.L ≤ K.map (MulAut.conj c.s⁻¹).toMonoidHom
    rw [←hsK,←c.exchange]
    exact map_mono hfirst
  let : IsElementaryAbelian 2 c.U₁ := c.first.elementary
  let : IsElementaryAbelian 2 c.U₂ := c.second.elementary
  refine ⟨hxK,hxKs,?_,?_⟩
  · exact Matrix.PSL3Two.moving_four_not_inner K c.U₁ eK ((map_subtype_le _).trans hfirst)
      (c.first.cubic_module_card c.cubic_first) g.z₁ c.x g.first_mem g.order_first hxK g.x_first c.noncommuting
  · exact Matrix.PSL3Two.moving_four_not_inner Ks c.U₂ (eS.symm.trans eK) ((map_subtype_le _).trans hLs)
      (c.second.cubic_module_card c.cubic_second) g.z₂ c.x g.second_mem g.order_second hxKs g.x_second
      (RankOne.second_noncommuting c.orbit)
end CFSG.Quasithin.Chapter2.DoubleA3.Noncentrality