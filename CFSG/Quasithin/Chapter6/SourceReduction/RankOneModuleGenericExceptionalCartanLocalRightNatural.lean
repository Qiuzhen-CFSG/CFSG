module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalLeftFixed
public import Theory.SpecificGroups.Alternating.SevenFiveSection
public import Theory.Representation.AlternatingSevenFiveSeed.Natural

/-!
# The actual right residual on the Cartan four-space

The A₇ action quotient maps the literal residual to A₅. The normalizing
Sylow subgroup marks the five-point section, whose restriction identifies
all of the original four-space with the natural SL₂(4) module. Faithful
irreducibility then proves that the residual moves the entire space.
The quotient maps retain their exact two-core kernels.

The final application uses the completed FF reduction with the original
universal Input and both Hall conditions. It supplies the natural-action
premise for the subsequent right block argument without assuming a
chosen module, splitting or coordinates.

Source: Aschbacher–Smith 5.1.13, printed pp.637–638, using C.1.28.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]

/-- The original residual has an actual A₅ image on the right four-space,
and its restriction is the natural SL₂(4) module. -/
theorem LocalA7Configuration.four_residual_natural
    {T : Sylow 2 G} {L W H A B Y X D K : Subgroup G} {n : ℕ}
    (a : LocalA7Configuration T L H X K)
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (d : LocalCartanWitness T H A Y X D) :
    let M := K ⊔ (T : Subgroup G)
    let U := (localOmegaModule T K).subgroupOf M
    let R := (residual H).subgroupOf M
    letI := (LocalOmega.reduced_internal a.reduced).normal
    letI := (LocalOmega.reduced_internal a.reduced).elementary
    ∃ q : M →* alternatingGroup (Fin 7), ∃ hq : Function.Surjective q,
      ∃ hk : q.ker = centralizer (U : Set M), q.ker = pCore 2 M ∧
        (q.subgroupMap R).ker = pCore 2 R ∧
        ∃ e : R.map q ≃* Matrix.SpecialLinearGroup (Fin 2) SL2FourNatural.F,
          ∃ f : Additive U ≃ₗ[ZMod 2] SL2FourNatural.V,
            ∀ (r : R.map q) v, f (NormalElementaryQuotient.representation U q hq hk r v) =
              specialLinearNatural 2 (e r) (f v) := by
  let M := K ⊔ (T : Subgroup G)
  let U := (localOmegaModule T K).subgroupOf M
  let R := (residual H).subgroupOf M
  let P := T.subtype (show (T : Subgroup G) ≤ M from le_sup_right)
  have hr : IsPReduced 2 U := LocalOmega.reduced_internal a.reduced
  let := hr.normal
  let := hr.elementary
  have hc := a.four h hH hgen c d
  obtain ⟨q,hq,hk,hcore⟩ := a.four_action h hc
  have hRM : residual H ≤ M := (d.residual_le.trans a.contains).trans le_sup_left
  let eR : R ≃* pResidual 2 H := (subgroupOfEquivOfLe hRM).trans
    ((pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective).symm
  obtain ⟨F,_,_,hF,⟨eF⟩⟩ := d.residual_linear
  obtain ⟨e5⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF
  let e : (R ⧸ pCore 2 R) ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.congr _ _ eR (pCore_map_iso 2 eR)).trans (eF.trans e5)
  have hkr : (q.subgroupMap R).ker = q.ker.subgroupOf R := by
    ext r
    exact Subtype.ext_iff
  have hkp : IsPGroup 2 (q.subgroupMap R).ker :=
    hkr.symm ▸ ((hcore.symm ▸ pCore_isPGroup).comap_subtype)
  have he := alternatingGroup.SevenFiveSection.image_twoCore_eq_bot_and_ker_eq q R hkp e
  let eq5 := alternatingGroup.SevenFiveSection.imageFiveEquiv q R hkp e
  have hPN : (P : Subgroup M) ≤ normalizer (R : Set M) := by
    intro t ht
    exact mem_normalizer_iff.mpr (fun r => mem_normalizer_iff.mp
      (le_normalizer_residual H (hH.1.1.2 ht)) r.val)
  have hN : (P.mapSurjective hq : Subgroup (alternatingGroup (Fin 7))) ≤
      normalizer (R.map q : Set (alternatingGroup (Fin 7))) :=
    (map_mono hPN).trans (R.le_normalizer_map q)
  have hd : Module.finrank (ZMod 2) (Additive U) = 4 := by
    apply Nat.pow_right_injective (by decide : 2 ≤ 2)
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive U)
    change Nat.card U = Nat.card (ZMod 2)^Module.finrank (ZMod 2) (Additive U) at hh
    rw [Nat.card_congr (subgroupOfEquivOfLe a.reduced.1).toEquiv,hc,Nat.card_zmod] at hh
    exact hh.symm
  obtain ⟨a5,f,hf⟩ := AlternatingSevenFiveSeed.natural_restriction
    (NormalElementaryQuotient.representation U q hq hk)
    (NormalElementaryQuotient.representation_injective U q hq hk) hd (R.map q) eq5
    (P.mapSurjective hq) hN
  exact ⟨q,hq,hk,hcore,he.2,a5,f,hf⟩


/-- The original residual moves the entire right four-space; there is no
additional residual-fixed summand or smaller chosen module. -/
theorem LocalA7Configuration.four_residual_full_movement
    {T : Sylow 2 G} {L W H A B Y X D K : Subgroup G} {n : ℕ}
    (a : LocalA7Configuration T L H X K)
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (d : LocalCartanWitness T H A Y X D) :
    ⁅localOmegaModule T K,residual H⁆ = localOmegaModule T K := by
  let M := K ⊔ (T : Subgroup G)
  let U := (localOmegaModule T K).subgroupOf M
  let R := (residual H).subgroupOf M
  have hr : IsPReduced 2 U := LocalOmega.reduced_internal a.reduced
  let := hr.normal
  let := hr.elementary
  obtain ⟨q,hq,hk,_,_,e,f,hf⟩ := a.four_residual_natural h hH hgen c d
  let ρ := NormalElementaryQuotient.representation U q hq hk
  let σ : Representation (ZMod 2) (R.map q) (Additive U) := ρ.comp (R.map q).subtype
  let F : ChapterB.QuasisimpleSource.BinaryField := {
    Carrier := SL2FourNatural.F
    degree := 2
    degree_pos := by decide
    card_eq := by rw [Nat.card_eq_fintype_card,SL2FourNatural.card_field]; decide }
  have hi : σ.IsIrreducible := ChapterB.QuasisimpleSource.ExtensionConsequences.irreducible_of_equiv
    ({groupEquiv := e,linearEquiv := f,intertwines := hf} :
      ChapterB.QuasisimpleSource.ActionEquiv σ (ChapterB.QuasisimpleSource.linearNatural F 2))
    (ChapterB.QuasisimpleSource.ExtensionConsequences.linearNatural_irreducible F (by decide : 2 ≤ 2))
  let : Nontrivial (R.map q) := (e.trans SL2FourNatural.alternatingFiveEquiv).toEquiv.nontrivial
  have hm := Representation.BinaryOffender.subspaceCommutator_top_eq_top_of_faithful_irreducible
    σ ((NormalElementaryQuotient.representation_injective U q hq hk).comp (R.map q).subtype_injective) hi
  change Representation.BinaryOffender.subspaceCommutator (ρ.comp (R.map q).subtype) ⊤ ⊤ = ⊤ at hm
  rw [Representation.BinaryOffender.subspaceCommutator_comp_map,
    ←MonoidHom.range_eq_map,range_subtype] at hm
  have he : ⁅U,R⁆ = U := by
    apply le_antisymm (commutator_le_left _ _) ?_
    intro u hu
    have ht : NormalElementaryQuotient.commutatorSpace U R = ⊤ :=
      (NormalElementaryQuotient.commutatorSpace_eq U q hq hk R).trans hm
    change Additive.ofMul (⟨u,hu⟩ : U) ∈ NormalElementaryQuotient.commutatorSpace U R
    rw [ht]
    exact Submodule.mem_top
  have hRM : residual H ≤ M := (d.residual_le.trans a.contains).trans le_sup_left
  have hh := congrArg (map M.subtype) he
  rwa [map_commutator,map_subgroupOf_eq_of_le a.reduced.1,map_subgroupOf_eq_of_le hRM] at hh

/-- The original noncentral source inputs supply the natural A₅ residual
support on the entire right omega commutator. -/
theorem localCartan_noncentral_right_full_movement
    {T : Sylow 2 G} {L W H A B Y X D : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X D) (hXC : ¬ X ≤ omegaCentralizer T) :
    ∃ K : Subgroup G, LocalA7Configuration T L H X K ∧
      Nat.card (localOmegaModule T K) = 16 ∧
      ⁅localOmegaModule T K,residual H⁆ = localOmegaModule T K := by
  obtain ⟨K,a⟩ := localCartan_ffReduction T L W n h H hH hgen A B c Y hY X D d hXC
  exact ⟨K,a,a.four h hH hgen c d,a.four_residual_full_movement h hH hgen c d⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
