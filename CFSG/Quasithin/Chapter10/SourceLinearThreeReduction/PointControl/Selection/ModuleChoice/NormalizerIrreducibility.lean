module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.Separation
public import CFSG.Quasithin.Chapter10.SourceA5OriginalModuleMarking.FactorKernel
public import Theory.Representation.BinaryConjugationSection.Irreducible
public import CFSG.Quasithin.ChapterE.Section03.Parameters.SectionNormalizer
public import Theory.GroupTheory.PResidual.PrimeToAction

/-!
# Minimality on the original component normalizer

An invariant moved subgroup of [V,L] generates at most its two original
conjugates under M. Minimality of the full module makes this orbit all of V;
crossed centralization then recovers [V,L] itself. Pulling invariant subspaces
back through the original central quotient proves irreducibility under N_M(L).

Faithful component coordinates extend to that literal normalizer, preserving
the entire fixed kernel and the original quotient map. The cubic residual
identity also makes every solvable image of N_M(L) prime to three. These are
the ambient inputs to the doubled-row exclusion, rather than extra module
classification assumptions.
Source: Aschbacher--Smith, D.3.21, 3.2.6 and10.1.3,
printed pp.204--207,581 and742.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
namespace CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

private theorem orbit_eq_pair_of_component_stabilizer
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (A : Subgroup G) (hA : D.maximalLocal ⊓ normalizer (L : Set G) ≤ normalizer (A : Set G)) :
    componentOrbit A D.maximalLocal = A ⊔ A.map (MulAut.conj t).toMonoidHom := by
  have hTM : (T : Subgroup G) ≤ D.maximalLocal := le_normalizer_componentOrbit L T
  have hpair := source_nonnormal_maximal_pair D (fun hn => htn (hn ht)) ht htn
  apply le_antisymm
  · apply iSup_le
    intro m
    rcases hpair m m.property with hm | hm
    · have he : A.map (MulAut.conj (m : G)).toMonoidHom = A :=
        mem_normalizer_iff_map_conj_eq.mp (hA ⟨m.property,mem_normalizer_iff_map_conj_eq.mpr hm⟩)
      rw [he]
      exact le_sup_left
    · have hs : t⁻¹ * m ∈ normalizer (L : Set G) := by
        apply mem_normalizer_iff_map_conj_eq.mpr
        calc
          _ = (L.map (MulAut.conj (m : G)).toMonoidHom).map (MulAut.conj t⁻¹).toMonoidHom := by
            rw [map_map]
            congr 1
            ext x
            simp [MulAut.conj_apply,mul_assoc]
          _ = L := by
            rw [hm,map_map]
            have he : (MulAut.conj t⁻¹).toMonoidHom.comp (MulAut.conj t).toMonoidHom = MonoidHom.id G := by
              ext x
              simp [MulAut.conj_apply,mul_assoc]
            rw [he,map_id]
      have he : A.map (MulAut.conj (m : G)).toMonoidHom =
          A.map (MulAut.conj t).toMonoidHom := by
        calc
          _ = (A.map (MulAut.conj (t⁻¹ * m)).toMonoidHom).map (MulAut.conj t).toMonoidHom := by
            rw [map_map]
            congr 1
            ext x
            simp [MulAut.conj_apply,mul_assoc]
          _ = _ := congrArg (map (MulAut.conj t).toMonoidHom)
            (mem_normalizer_iff_map_conj_eq.mp
              (hA ⟨D.maximalLocal.mul_mem (D.maximalLocal.inv_mem (hTM ht)) m.property,hs⟩))
      rw [he]
      exact le_sup_right
  · exact sup_le (le_componentOrbit A D.maximalLocal)
      (le_iSup (fun m : D.maximalLocal => A.map (MulAut.conj (m : G)).toMonoidHom) ⟨t,hTM ht⟩)

/-- Minimality of the full module descends to the original separated moved
factor under its actual component normalizer. -/
theorem minimal_moved_eq_of_normalizer_moved
    (hmin : D.IsMinimalFullModule)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    (A : Subgroup G) (hAW : A ≤ ⁅D.fullModule,L⁆)
    (hAN : D.maximalLocal ⊓ normalizer (L : Set G) ≤ normalizer (A : Set G))
    (hmove : ⁅A,L⁆ ≠ ⊥) : A = ⁅D.fullModule,L⁆ := by
  let U := componentOrbit A D.maximalLocal
  have hLM : L ≤ D.maximalLocal := (le_componentOrbit L T).trans (localOrbit T L).le_normalizer
  have hLA : L ≤ normalizer (A : Set G) := (le_inf hLM L.le_normalizer).trans hAN
  have hWV : ⁅D.fullModule,L⁆ ≤ D.fullModule :=
    le_normalizer_iff_commutator_le_left.mp (hLM.trans D.maximalLocal_normalizes_fullModule)
  have hUV : U ≤ D.fullModule := iSup_conjugates_le_of_le_normalizer _ _ _
    (hAW.trans hWV) D.maximalLocal_normalizes_fullModule
  have hU : U = D.fullModule := source_minimal_fullModule_eq_of_normal_moved D hmin U
    (le_normalizer_componentOrbit A D.maximalLocal) hUV (by
      intro hz
      exact hmove (bot_unique ((commutator_mono (le_componentOrbit A D.maximalLocal) le_rfl).trans_eq hz)))
  have hgen : A.map (MulAut.conj t).toMonoidHom ⊔ A = D.fullModule := by
    rw [sup_comm,←orbit_eq_pair_of_component_stabilizer D ht htn A hAN]
    exact hU
  have hc : A.map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G) :=
    (map_mono hAW).trans hcross
  have hAL : A ≤ normalizer (L : Set G) :=
    hAW.trans ((source_full_moved_le_component D).trans L.le_normalizer)
  have he := commutator_eq_of_centralizing_sup hgen hc hAL
  rw [commutator_comm L A,commutator_comm L D.fullModule] at he
  exact le_antisymm hAW (he ▸ le_normalizer_iff_commutator_le_left.mp hLA)

/-- The central kernel is retained in the original moved-factor minimality. -/
theorem minimal_moved_eq_or_le_fixed
    (hmin : D.IsMinimalFullModule)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    (A : Subgroup G) (hAW : A ≤ ⁅D.fullModule,L⁆)
    (hAN : D.maximalLocal ⊓ normalizer (L : Set G) ≤ normalizer (A : Set G)) :
    A = ⁅D.fullModule,L⁆ ∨ A ≤ sourceMovedFixed D := by
  by_cases hm : ⁅A,L⁆ = ⊥
  · exact Or.inr (le_inf hAW (commutator_eq_bot_iff_le_centralizer.mp hm))
  · exact Or.inl (minimal_moved_eq_of_normalizer_moved D hmin ht htn hcross A hAW hAN hm)

/-- Every literal quotient action of the component normalizer is irreducible
on the original moved subgroup modulo its complete fixed kernel. -/
theorem moved_normalizer_section_irreducible
    (hmin : D.IsMinimalFullModule)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Nontrivial V]
    (ρ : Representation (ZMod 2) (D.maximalLocal ⊓ normalizer (L : Set G) : Subgroup G) V)
    (c : BinaryConjugationSection (D.maximalLocal ⊓ normalizer (L : Set G))
      ⁅D.fullModule,L⁆ (sourceMovedFixed D) ρ) : ρ.IsIrreducible := by
  apply c.irreducible_of_subgroup_minimal
  intro A hAW hAN
  exact minimal_moved_eq_or_le_fixed D hmin ht htn hcross A hAW hAN

/-- A faithful marking of the component quotient extends to the literal
component normalizer, and minimality makes this extended action irreducible. -/
theorem exists_irreducible_moved_normalizer
    (hmin : D.IsMinimalFullModule)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    {J V : Type*} [Group J] [AddCommGroup V] [Module (ZMod 2) V] [Nontrivial V]
    (σ : Representation (ZMod 2) J V) (hf : Function.Injective σ)
    (e : (L ⧸ pCore 2 L) ≃* J)
    (c : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
      (σ.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) :
    ∃ (ρ : Representation (ZMod 2) (D.maximalLocal ⊓ normalizer (L : Set G) : Subgroup G) V)
      (f : (D.maximalLocal ⊓ normalizer (L : Set G) : Subgroup G) →*
        BinaryOffender.linearNormalizer σ),
      ρ.IsIrreducible ∧
      (∀ g v, BinaryOffender.normalizerRepresentation σ (f g) v = ρ g v) ∧
      Nonempty (BinaryConjugationSection (D.maximalLocal ⊓ normalizer (L : Set G))
        ⁅D.fullModule,L⁆ (sourceMovedFixed D) ρ) := by
  let W := ⁅D.fullModule,L⁆
  let N := D.maximalLocal ⊓ normalizer (L : Set G)
  let : IsElementaryAbelian 2 W := source_original_full_moved_elementary D
  let π := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hLN : L ≤ N := le_inf ((le_componentOrbit L T).trans (localOrbit T L).le_normalizer) L.le_normalizer
  have hNW : N ≤ normalizer (W : Set G) := by
    intro g hg
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom = ⁅D.fullModule,L⁆
    have hV : D.fullModule.map (MulAut.conj g).toMonoidHom = D.fullModule :=
      mem_normalizer_iff_map_conj_eq.mp (D.maximalLocal_normalizes_fullModule hg.1)
    have hL : L.map (MulAut.conj g).toMonoidHom = L :=
      mem_normalizer_iff_map_conj_eq.mp hg.2
    rw [map_commutator,hV,hL]
  have hNZ : N ≤ normalizer (sourceMovedFixed D : Set G) :=
    (le_inf (show N ≤ normalizer (L : Set G) from inf_le_right) hNW).trans
      (source_original_moved_fixed_normalizer D)
  have hLZ : L ≤ normalizer (sourceMovedFixed D : Set G) := hLN.trans hNZ
  have hkernel : commutatorPreimage L W (sourceMovedFixed D) = L.pCoreIn 2 := by
    have hh := c.action_kernel_map hLZ
    rw [MonoidHom.ker_comp_of_injective _ _ hf,
      MonoidHom.ker_comp_of_injective _ e.toMonoidHom e.injective,
      QuotientGroup.ker_mk'] at hh
    exact hh.symm
  have hkL : commutatorPreimage L W (sourceMovedFixed D) ≤ centralizer (W : Set G) := by
    rw [hkernel]
    exact (source_component_core_centralizes_fullModule D).trans (centralizer_le
      (le_normalizer_iff_commutator_le_left.mp
        (((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
          D.maximalLocal_normalizes_fullModule)))
  have hk : commutatorPreimage N W (sourceMovedFixed D) ≤ centralizer (W : Set G) :=
    commutatorPreimage_le_centralizer_of_fully_moved N L W (sourceMovedFixed D)
      hLN inf_le_right hNW hNZ inf_le_right (source_full_moved_eq_commutator D) hkL
  have hNN : N ⊓ normalizer (W : Set G) = N := inf_eq_left.mpr hNW
  obtain ⟨τ,ι,_,hιτ,hact⟩ := ChapterE.exists_local_section_normalizer L W (sourceMovedFixed D)
    N σ π hπ c hLN (inf_le_left.trans inf_le_right) (inf_le_left.trans hNZ) (by
      simpa only [hNN] using hk)
  let q := (ChapterE.localNormalizerAction W N).comp (inclusion (le_inf le_rfl hNW))
  let ρ := τ.comp q
  let cN : BinaryConjugationSection N W (sourceMovedFixed D) ρ := {
    section_le := (source_full_moved_le_component D).trans hLN
    kernel_le := c.kernel_le
    normalized := hNW
    coordinates := c.coordinates
    onto := c.onto
    kernel_eq := c.kernel_eq
    equivariant := fun g w => (hact (inclusion (le_inf le_rfl hNW) g) w).symm }
  exact ⟨ρ,ι.comp q,moved_normalizer_section_irreducible D hmin ht htn hcross ρ cN,
    fun g v => hιτ (q g) v,⟨cN⟩⟩

/-- Every solvable image of the original component normalizer has order
prime to three, from the actual cubic residual of the maximal local group. -/
theorem normalizer_solvable_image_three_free
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hd : 3 ∣ Nat.card (L ⧸ pCore 2 L))
    {S : Type*} [Group S] [Group.IsSolvable S]
    (f : (D.maximalLocal ⊓ normalizer (L : Set G) : Subgroup G) →* S) :
    Nat.Coprime 3 (Nat.card f.range) := by
  let N := D.maximalLocal ⊓ normalizer (L : Set G)
  let R := localOrbit T L
  have hRN : R ≤ N := le_inf R.le_normalizer (source_nonnormal_orbit_le_normalizer D hn)
  let : Group.IsPerfect L := Chapter1.mem_L_isPerfect D.maximal.1
  let : Group.IsPerfect R := isPerfect_iSup_conjugates L T
  let a := f.comp (inclusion hRN)
  have ha : a = 1 := by
    let : Group.IsPerfect a.range := Group.IsPerfect.ofSurjective (f := a.rangeRestrict) a.rangeRestrict_surjective
    have hs : Subsingleton a.range := by
      by_contra! hs
      exact Group.IsPerfect.not_isSolvable a.range inferInstance
    ext x
    exact congrArg Subtype.val (hs.elim (a.rangeRestrict x) 1)
  apply coprime_card_range_of_primeToResidual_le_ker 3 f
  intro x hx
  have hxR : (x : G) ∈ R := by
    have hle := embedded_primeToResidual_mono 3 (show N ≤ D.maximalLocal from inf_le_left)
    rw [source_nonnormal_cubic_residual D hn hd] at hle
    exact hle (mem_map_of_mem N.subtype hx)
  have hh := DFunLike.congr_fun ha (⟨x,hxR⟩ : R)
  exact hh

end CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
