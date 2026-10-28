module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.FixedCoordinates
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.ModuleCover
public import Theory.ElementaryAbelian.GeneratorRank

/-!
# The original-section cover and the preliminary rank bound

The precise earlier 14.5.15(4) assertion that O₂(H) acts trivially on U/V₁
constructs a descended action through the same H → H/O₂(H) → S₅. Its
alternating restriction retains the natural marking and the original
projection p. K-fixedness and K-indecomposability therefore give the checked
universal-cover bound dim(ker p) ≤ 2 and the same-p upper complement.

The restricted coordinate homomorphism U₀ → ker p is surjective, with
kernel exactly V₁. Consequently |U₀| = 2 |ker p| and primeRank 2 U₀ ≤ 3.
This is the preliminary bound from 14.7.64, not the rank-two conclusion of
14.7.70. The rank-three Goldschmidt exclusion is still required.

The only extra action input is stated literally as triviality on pCore 2 H;
its source producer is qt-14-05, with final earlier-input discharge owned
by qt-14-07-local-critical-fusion. No equality O₂(K)=O₂(H) is used.

Source: Aschbacher–Smith, combined manuscript, 1 March 2004,
14.5.15(4), p.1017; 14.7.64 and 14.7.70, pp.1069, 1073.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Subgroup Representation Chapter12.Section08
open Representation.OneCohomology
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
namespace Data
variable (d : Data T L V F W)

/-- Descent retains the same original action, quotient marking and coordinates.
Its existence is the earlier O₂(H)-centralization assertion of 14.5.15(4). -/
structure ActionDescent where
  action : Representation (ZMod 2) ChapterJ.S5 W
  original : ∀ h : F.H, action (d.qH h) = d.action h

/-- Construct descent from the precise earlier two-core centralization,
rather than assuming that the action factors through an unrelated quotient. -/
def actionDescentOfCore
    (hcore : ∀ h : F.H, h ∈ pCore 2 F.H → d.action h = 1) : d.ActionDescent := by
  have hk : d.qH.ker ≤ d.action.asGroupHom.ker := by
    intro h hh
    apply MonoidHom.mem_ker.mpr
    apply Units.ext
    change d.action h = 1
    apply hcore h
    rw [d.qH_ker] at hh
    exact (mem_map_iff_mem F.H.subtype_injective).mp hh
  let a : ChapterJ.S5 →* Units (W →ₗ[ZMod 2] W) :=
    d.qH.liftOfSurjective d.qH_surjective ⟨d.action.asGroupHom, hk⟩
  refine ⟨(Units.coeHom _).comp a, ?_⟩
  intro h
  change (a (d.qH h) : W →ₗ[ZMod 2] W) = d.action h
  have ha : a (d.qH h) = d.action.asGroupHom h :=
    d.qH.liftOfRightInverse_comp_apply (Function.surjInv d.qH_surjective)
      (Function.rightInverse_surjInv d.qH_surjective) ⟨d.action.asGroupHom, hk⟩ h
  exact congrArg Units.val ha

namespace ActionDescent
variable {d} (s : d.ActionDescent)

/-- The exact original projection, now viewed with the descended actor. -/
def projection : s.action.IntertwiningMap d.naturalQuotient.action where
  toLinearMap := d.projection.toLinearMap
  isIntertwining' := by
    intro g
    obtain ⟨h, rfl⟩ := d.qH_surjective g
    apply LinearMap.ext
    intro w
    change d.projection (s.action (d.qH h) w) = d.naturalQuotient.action (d.qH h) (d.projection w)
    rw [s.original]
    exact LinearMap.congr_fun (d.projection.isIntertwining' h) w

theorem kernel_fixed : s.projection.toLinearMap.ker ≤
    fixed (s.action.comp (alternatingActor d.naturalQuotient)) := by
  intro w hw g
  have hg : alternatingActor d.naturalQuotient g ∈
      ((K F).subgroupOf F.H).map d.qH := by
    rw [d.K_image]
    exact (d.naturalQuotient.marking g).property
  obtain ⟨h, hh, he⟩ := hg
  change s.action (alternatingActor d.naturalQuotient g) w = w
  rw [← he, s.original]
  have hw' : w ∈ Representation.invariants (d.action.comp ((K F).subgroupOf F.H).subtype) :=
    d.fixed_kernel ▸ hw
  exact hw' ⟨h, hh⟩

theorem indecomposable (A B : Submodule (ZMod 2) W)
    (hA : ∀ g w, w ∈ A → s.action (alternatingActor d.naturalQuotient g) w ∈ A)
    (hB : ∀ g w, w ∈ B → s.action (alternatingActor d.naturalQuotient g) w ∈ B)
    (hc : IsCompl A B) : A = ⊥ ∨ B = ⊥ := by
  have lift (k : (K F).subgroupOf F.H) :
      ∃ g : Representation.SL2FourNatural.SL, alternatingActor d.naturalQuotient g = d.qH k := by
    have hk : d.qH k ∈ alternatingGroup (Fin 5) := by
      rw [← d.K_image]
      exact mem_map_of_mem d.qH k.property
    obtain ⟨g, hg⟩ := d.naturalQuotient.marking.surjective ⟨d.qH k, hk⟩
    exact ⟨g, congrArg Subtype.val hg⟩
  apply d.indecomposable A B _ _ hc
  · intro k w hw
    obtain ⟨g, hg⟩ := lift k
    have h := hA g w hw
    rwa [hg, s.original] at h
  · intro k w hw
    obtain ⟨g, hg⟩ := lift k
    have h := hB g w hw
    rwa [hg, s.original] at h

include s in
theorem kernel_finrank_le_two : Module.finrank (ZMod 2) d.projection.toLinearMap.ker ≤ 2 := by
  let : Finite (Multiplicative W) := Finite.of_surjective _ d.conjugationSection.onto
  let : Finite W := Finite.of_equiv (Multiplicative W) Multiplicative.toAdd
  let : FiniteDimensional (ZMod 2) W := Module.Finite.of_finite
  let p := restrictedProjection d.naturalQuotient s.projection
  exact SL2FourCentralCover.kernel_finrank_le_two p
    (SL2FourCentralCover.isCover_of_natural_indecomposable p d.projection_onto
      s.kernel_fixed s.indecomposable)

/-- The complement computation on the original H-action and the same p.
The actor hypothesis only specifies the chosen nonidentity upper element. -/
theorem original_upper_complement (h : F.H) (t : Representation.SL2FourNatural.F)
    (ht : t ≠ 0)
    (hh : d.qH h = alternatingActor d.naturalQuotient (Representation.SL2FourNatural.upper t)) :
    Disjoint (d.action h - LinearMap.id).range d.projection.toLinearMap.ker ∧
      SL2CentralExtension.upperFixed (s.action.comp (alternatingActor d.naturalQuotient)) =
        (d.action h - LinearMap.id).range ⊔ d.projection.toLinearMap.ker := by
  have he : d.action h =
      s.action (alternatingActor d.naturalQuotient (Representation.SL2FourNatural.upper t)) := by
    rw [← hh, s.original]
  rw [he]
  exact original_section_upper_complement d.naturalQuotient s.projection d.projection_onto
    s.kernel_fixed s.indecomposable t ht

end ActionDescent

/-- The literal point kernel adds exactly one binary dimension to U₀/V₁. -/
theorem U₀_card : Nat.card d.U₀ = Nat.card d.projection.toLinearMap.ker * 2 := by
  rw [card_eq_card_quotient_mul_card_subgroup d.fixedCoordinates.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective d.fixedCoordinates
      d.fixedCoordinates_surjective).toEquiv, d.fixedCoordinates_ker,
    Nat.card_congr (subgroupOfEquivOfLe d.point_le_U₀).toEquiv,
    F.card 1 (by decide)]
  rfl

/-- The preliminary bound from 14.7.64 is on the actual elementary subgroup. -/
theorem U₀_rank_le_three (s : d.ActionDescent) : primeRank 2 d.U₀ ≤ 3 := by
  let : IsElementaryAbelian 2 d.U₀ := d.U₀_elementary
  let : Finite (Multiplicative W) := Finite.of_surjective _ d.conjugationSection.onto
  let : Finite W := Finite.of_equiv (Multiplicative W) Multiplicative.toAdd
  have hc : Nat.card d.projection.toLinearMap.ker ≤ 4 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    exact (Nat.pow_le_pow_right (by decide : 1 ≤ 2) s.kernel_finrank_le_two).trans_eq (by decide)
  apply IsElementaryAbelian.primeRank_le_of_card_le
  rw [d.U₀_card]
  exact (Nat.mul_le_mul_right 2 hc).trans_eq (by decide)

/-- Source 14.5.15(4) suffices for the preliminary rank-three bound. -/
theorem U₀_rank_le_three_of_core_centralizes
    (hcore : ∀ h : F.H, h ∈ pCore 2 F.H → d.action h = 1) : primeRank 2 d.U₀ ≤ 3 :=
  d.U₀_rank_le_three (d.actionDescentOfCore hcore)

end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
