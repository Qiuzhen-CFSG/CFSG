module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.CriticalPairs

/-!+# The remaining binary module contracts for the common MS93 reduction

`ModuleFacts` records outputs still required from the binary specializations of
Section 3 and (4.1). It has no constructor here from `LocalSource`. In particular
the actual natural-module isomorphism is a proof obligation, not a source
hypothesis. This interface lets the subsequent escape argument be developed
conditionally while its module inputs are proved independently.

The relative index `Q.relIndex U` means [U : U ∩ Q], so the critical-pair
clauses are the literal image orders in (3.5). The last clause is the binary
case of (3.9), expressed as centrality of the derived subgroup of the
radius-two V. These groups are not the global commutator core.

For (4.1)'s notation c(Z_alpha)=1, the triple commutator is already trivial
by (2.1)(iv). Thus its quotient by [Z_alpha,Q_alpha] is Z_alpha itself, and
the displayed decomposition, disjointness and actual natural action give
the full required meaning; no unexplained c-certificate is used.

Source: Meierfrankenfeld--Stellmacher (1993), (3.2)--(3.3), (3.5), (3.9),
(4.0)--(4.1), printed pp.863--870, 879, 881--882.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93
variable {M : Type*} [Group M] {L R : Subgroup M}

/-- Later source consequences to be proved under b > 2. They contain no
conclusion about the center or exponent of the commutator core. -/
structure ModuleFacts (source : LocalSource L R) (geometry : Geometry R) where
  X_eq_Z : ∀ a, color R a = false → X R a = Z R a
  natural : NaturalU R source.projection
  full_commutation : ⁅U R (alpha R), Ltilde R (alpha R)⁆ = U R (alpha R)
  decomposition : Z R (alpha R) = U R (alpha R) ⊔
    (Z R (alpha R) ⊓ centralizer (Ltilde R (alpha R) : Set (FreeAmalgam R)))
  disjoint : Disjoint (U R (alpha R))
    (Z R (alpha R) ⊓ centralizer (Ltilde R (alpha R) : Set (FreeAmalgam R)))
  critical_U_index : ∀ a (ha : color R a = false) a',
    CriticalPair R a a' (geometry.exists_critical a ha) →
      (Q R a').relIndex (U R a) = (Q R a).relIndex (U R a')
  critical_Z_commutator_card : ∀ a (ha : color R a = false) a',
    CriticalPair R a a' (geometry.exists_critical a ha) →
      (Q R a').relIndex (Z R a) = 4 →
        Nat.card (⁅Z R a, Z R a'⁆ : Subgroup (FreeAmalgam R)) = 2
  b_four_class_two : geometry.b R = 4 → ∀ a, color R a = false →
    ⁅⁅V R a, V R a⁆, V R a⁆ = ⊥

/-- Source (4.2)(ii), with normality only inside the actual local stabilizer. -/
def NormalizationTransfer (R : Subgroup M) : Prop :=
  ∀ a, color R a = false → ∀ Y : Subgroup (FreeAmalgam R), Y ≤ Q R a →
    (Y.subgroupOf (stabilizer R a)).Normal →
    ⁅Vcirc R a, Y⁆ ≤ fixedCore R a → ⁅V R a, Y⁆ ≤ fixedCore R a

/-- Source (4.3), for every critical pair and the point two steps before
its endpoint on the geodesic. This is a target, not an available theorem. -/
def CriticalEscape (R : Subgroup M) (geometry : Geometry R) : Prop :=
  ∀ a (ha : color R a = false) a',
    CriticalPair R a a' (geometry.exists_critical a ha) →
    ∀ c, (cosetGraph R).dist c a' = 2 →
      (cosetGraph R).dist a c + 2 = (cosetGraph R).dist a a' → ¬ V R a ≤ Q R c

/-- The order is transported through the actual natural-model equivalence. -/
theorem NaturalU.card {π : M →* SL} (natural : NaturalU R π) :
    Nat.card (U R (alpha R)) = 8 := by
  rw [Nat.card_congr natural.equiv.toEquiv]
  change Nat.card (Fin 3 → ZMod 2) = 8
  simp only [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  norm_num

/-- The first clause in the source's expanded c(Z_alpha)=1 notation. -/
theorem Geometry.Z_triple_commutator (geometry : Geometry R)
    (a : Vertex R) (ha : color R a = false) : ⁅⁅Z R a, Q R a⁆, Ltilde R a⁆ = ⊥ := by
  rw [geometry.centralizes a ha]
  simp

end CFSG.Quasithin.ChapterC.BinaryMS.MS93
