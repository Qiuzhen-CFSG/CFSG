module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.A5Factor
import all Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.A5Factor
public import Theory.SpecificGroups.Alternating.FiveChiefDegree
public import Theory.GroupTheory.SolvableResidual.NormalSupplement
public import Theory.GroupTheory.PCoreFrattiniTransport

/-!
# The same A₅ residual inside the literal J₄ max4

A perfect subgroup with two-core quotient A₅ has trivial projection to
SL₃(2), since every nontrivial image has order divisible by five. Its
perfect five-point image is contained in A₅, and the two-group kernel
forces equality with the literal A₅ × 1 factor.

If the full Sylow normalizes this subgroup, the ambient two-core does as
well. The subgroup is therefore the solvable residual of the marked full
preimage, which is normal in max4. This recovers and normalizes the same
subgroup without identifying it with the larger full preimage.

The internal `import all` is intentional: this proof extension uses the
private bodies of the two marked subgroups without changing their APIs.
The actual quotient maps and imported ATLAS provenance are retained.
Source: Aschbacher--Smith A.3.14(10) and 5.1.13, printed pp.49--50,637.
-/

public noncomputable section
open Subgroup
namespace Janko4.LocalStructure.SymmetricLinear
attribute [local irreducible] modelGroup matrixA matrixB max4Subgroup

private theorem perfect_twoPerfect {G : Type*} [Group G] [Finite G]
    [Group.IsPerfect G] : IsPPerfect 2 G := by
  intro N hN hq
  let := hN
  by_contra hn
  let : Nontrivial (G ⧸ N) := QuotientGroup.nontrivial_iff.mpr hn
  exact Group.IsPerfect.not_isNilpotent (G ⧸ N) hq.isNilpotent

/-- The literal quotient image is exactly the alternating-five factor. -/
theorem perfect_five_projection (R : Subgroup max4Subgroup) [Group.IsPerfect R]
    (e : (R ⧸ pCore 2 R) ≃* alternatingGroup (Fin 5)) :
    R.map max4Projection = a5Factor := by
  let f := max4Projection.comp R.subtype
  let b := (MonoidHom.snd (Equiv.Perm (Fin 5))
    (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))).comp f
  have hb : b = 1 := by
    by_contra hn
    have hd := (alternatingGroup.FiveChiefDegree.five_dvd_card_range
      perfect_twoPerfect e b hn).trans b.range.card_subgroup_dvd_card
    rw [Atlas.Comparisons.Exceptional.sl3Two_card] at hd
    norm_num at hd
  have hfirst : (R.map max4Projection).map (MonoidHom.fst _ _) ≤ alternatingGroup (Fin 5) := by
    rw [← R.commutator_eq_self, map_commutator, map_commutator]
    exact (commutator_mono le_top le_top).trans alternatingGroup.commutator_perm_le
  have hle : R.map max4Projection ≤ a5Factor := by
    rintro x ⟨r,hr,rfl⟩
    refine ⟨hfirst (mem_map_of_mem _ (mem_map_of_mem _ hr)),?_⟩
    exact congrArg (fun k : R →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) =>
      k ⟨r,hr⟩) hb
  let g := max4Projection.subgroupMap R
  have hk : IsPGroup 2 g.ker := by
    have hle : g.ker ≤ max4Projection.ker.comap R.subtype := by
      intro x hx
      exact congrArg Subtype.val hx
    exact (max4Projection_kernel_isTwoGroup.comap_of_injective _ R.subtype_injective).to_le hle
  let a := g.pCoreQuotientEquiv (max4Projection.subgroupMap_surjective R) hk
  have hc : Nat.card ((R.map max4Projection) ⧸ pCore 2 (R.map max4Projection)) = 60 := by
    rw [← Nat.card_congr a.toEquiv, Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hd : 60 ∣ Nat.card (R.map max4Projection) := by
    rw [← hc]
    exact (pCore 2 (R.map max4Projection)).card_quotient_dvd_card
  apply eq_of_le_of_card_ge hle
  have hfactor : Nat.card a5Factor = 60 := by
    change Nat.card ((alternatingGroup (Fin 5)).prod
      (⊥ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)))) = 60
    rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod,
      Subgroup.card_bot, mul_one, nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  rw [hfactor]
  exact Nat.le_of_dvd Nat.card_pos hd

/-- Recover the same perfect subgroup as the residual, not the full preimage. -/
theorem perfect_five_eq_residual_preimage (R : Subgroup max4Subgroup)
    [Group.IsPerfect R] (e : (R ⧸ pCore 2 R) ≃* alternatingGroup (Fin 5))
    (hn : pCore 2 max4Subgroup ≤ normalizer (R : Set max4Subgroup)) :
    R = (solvableResidual a5Preimage).map a5Preimage.subtype := by
  have he : R ⊔ pCore 2 max4Subgroup = a5Preimage := by
    rw [← max4Projection_kernel_eq_twoCore, ← comap_map_eq,
      perfect_five_projection R e]
    rfl
  let : Group.IsNilpotent (pCore 2 max4Subgroup) := pCore_isPGroup.isNilpotent
  have hh := map_solvableResidual_sup_eq_of_perfect_normalized R (pCore 2 max4Subgroup) hn
  rw [he] at hh
  exact hh.symm

/-- The native whole max4 normalizes any such full-Sylow-normalized perfect A₅ section. -/
theorem perfect_five_normal (S : Sylow 2 max4Subgroup) (R : Subgroup max4Subgroup)
    [Group.IsPerfect R] (e : (R ⧸ pCore 2 R) ≃* alternatingGroup (Fin 5))
    (hn : (S : Subgroup max4Subgroup) ≤ normalizer (R : Set max4Subgroup)) : R.Normal := by
  rw [perfect_five_eq_residual_preimage R e (pCore_isPGroup.le_sylow_of_normal S |>.trans hn)]
  infer_instance

/-- Ambient form retaining the original full Sylow and the same subgroup. -/
theorem max4_normalizes_perfect_five (S : Sylow 2 Model) (R : Subgroup Model)
    [Group.IsPerfect R] (e : (R ⧸ pCore 2 R) ≃* alternatingGroup (Fin 5))
    (hn : (S : Subgroup Model) ≤ normalizer (R : Set Model))
    (hS : (S : Subgroup Model) ≤ max4Subgroup) (hR : R ≤ max4Subgroup) :
    max4Subgroup ≤ normalizer (R : Set Model) := by
  let d := subgroupOfEquivOfLe hR
  let : Group.IsPerfect (R.subgroupOf max4Subgroup) :=
    Group.IsPerfect.ofSurjective (f := d.symm.toMonoidHom) d.symm.surjective
  have he := (QuotientGroup.congr _ _ d (pCore_map_iso 2 d)).trans e
  apply (normal_subgroupOf_iff_le_normalizer hR).mp
  apply perfect_five_normal (S.subtype hS) _ he
  intro x hx
  apply mem_normalizer_iff.mpr
  intro r
  exact mem_normalizer_iff.mp (hn hx) (r : Model)

end Janko4.LocalStructure.SymmetricLinear
