module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.InvolutionRank
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.CentralizerGeometry
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.GaschutzComplement.SourceSylow.Application

/-!
# Conditional source assembly of 14.4.7

Work with the genuine extraspecial subgroup U from Hypothesis 14.3.10,
the literal H/O₂(H) action on U/Z(U), and the actual transporter g. The
explicit conditional inputs are the earlier 12.8/14.3 geometry and natural
action, G.2.5 as invoked by 12.8.8(4), and alternatives (3)--(6) of 14.4.2.
They remain with the outer source assembly; none asserts a conclusion of
14.4.6 or 14.4.7. In particular `EarlierComplement` is not a replacement
encoding of Hypothesis 14.3.10 or a source-specific splitting certificate.

The proved model inspection discharges the rank obstruction. Extraspecial
lifting, the hyperplane commutator bound, model generation and uniqueness
then give C_D(L)=1 for D=C_{Hᵍ}(Uᵍ). Symmetry supplies the bounds on all
L-conjugates of U. The natural G.2.5 action constructs the literal Sylow
Uᵍ C_U(V₂) C_{Uˡ}(V), and the proved binary Gaschütz consequence gives
C_D(L) as a relative complement to V₁ᵍ in D and the multiplication
isomorphism V × C_D(L) ≃ DV. Thus D=V₁ᵍ, Qᵍ=Uᵍ, and Q=U.

Right conjugation always means g⁻¹Hg. Q is `H.pCoreIn 2`, the embedded
two-core of H, not an ambient normal subgroup of G. The old conditional
interfaces in `LargerDimension` are neither changed nor used here.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
14.4.6--7, printed pp.1008--1009; 12.8.8(4), G.2.5 and 14.3.16.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore
open Subgroup CentralizerGeometry GaschutzComplement
open scoped Pointwise

universe w
variable {G V : Type*} [Group G]
  [AddCommGroup V] [Module (ZMod 2) V]
  {H U V₁ V₂ L : Subgroup G} {g : G} [(U.subgroupOf H).Normal]

/-- The earlier 12.8/14.3 natural-module geometry and G.2.5 data used in
14.4.7. These are explicit conditional source inputs, not a replacement for
Hypothesis 14.3.10. No centralizer bound, rank obstruction, Sylow certificate,
complement or two-core equality is a field. -/
structure EarlierComplement
    (d : EarlierGeometry (V := V) H U V₁ V₂ L g) (V₀ : Subgroup G) (l : G) where
  l_mem : l ∈ L
  V_le_U : V₀ ≤ U
  span_eq : conjugateSpan U L = L ⊔ U
  span_normalizes : conjugateSpan U L ≤ normalizer (V₀ : Set G)
  frame : SourceNaturalFrame U V₀ V₁ V₂ L g l span_normalizes
  U_image : (U.subgroupOf (conjugateSpan U L)).map frame.actor =
    Matrix.PSL3Two.SourceFlag.secondRadical
  Ug_image : ((rightConjugate U g).subgroupOf (conjugateSpan U L)).map frame.actor =
    Matrix.PSL3Two.MarkedAutomorphisms.pointV
  kernel : (centralizer (V₀ : Set G)).subgroupOf (conjugateSpan U L) =
    pCore 2 (conjugateSpan U L)
  core_product : (pCore 2 (conjugateSpan U L) : Set (conjugateSpan U L)) =
    (U.subgroupOf (conjugateSpan U L) ⊓ pCore 2 (conjugateSpan U L) : Set _) *
    ((rightConjugate U g).subgroupOf (conjugateSpan U L) ⊓ pCore 2 (conjugateSpan U L) : Set _) *
    ((rightConjugate U l).subgroupOf (conjugateSpan U L) ⊓ pCore 2 (conjugateSpan U L) : Set _)
  fixed : V₀ ⊓ centralizer (L : Set G) = ⊥
  points : ∀ x ∈ L, conjugate V₁ x = conjugate V₁ g ∨
    ∃ t ∈ L, t ∈ conjugate H g ∧ conjugate V₁ x = conjugate V₁ t

/-- The G.2.5 kernel normalizes U: it centralizes V₀, hence V₁, and
therefore lies in H. Thus this normalization is not an additional input. -/
theorem EarlierComplement.core_normalizes
    {d : EarlierGeometry (V := V) H U V₁ V₂ L g} {V₀ : Subgroup G} {l : G}
    (earlier : EarlierComplement d V₀ l) :
    pCore 2 (conjugateSpan U L) ≤
      normalizer (U.subgroupOf (conjugateSpan U L) : Set (conjugateSpan U L)) := by
  intro x hx
  have hxC : (x : G) ∈ centralizer (V₀ : Set G) := by
    change x ∈ (centralizer (V₀ : Set G)).subgroupOf (conjugateSpan U L)
    rwa [earlier.kernel]
  have hxH : (x : G) ∈ H := by
    rw [d.H_eq_centralizer]
    exact centralizer_le earlier.frame.line_one_le hxC
  apply Subgroup.mem_normalizer_iff.mpr
  intro u
  exact Subgroup.mem_normalizer_iff.mp (d.normalizes hxH) u.val

variable [Finite G] [Module.Finite (ZMod 2) V] [IsExtraspecial 2 U]

/-- Conditional source Lemma 14.4.7, with the literal complement retained.
The rank obstruction, centralizer uniqueness, symmetric bounds and the
three-factor Sylow property are all discharged in the proof. The remaining
parameters are precisely earlier-source geometry and the alternatives of
14.4.2; in particular U=O₂(H) and a splitting are not inputs. -/
theorem EarlierGeometry.source_twoCore_eq
    (d : EarlierGeometry (V := V) H U V₁ V₂ L g)
    (models : ActionAlternative.{w} d.action)
    (h1442 : ∀ t ∈ L, t ∈ normalizer (V₂ : Set G) → t ∉ H →
      let X := ((conjugate (W U V₂) t).subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))
      ModelGeneration.SourceAlternative X (Module.finrank (ZMod 2) V) ∧
        IsElementaryAbelian 2 X ∧ Nat.card X = 2 ^ (Module.finrank (ZMod 2) V / 2 - 1))
    (T : Sylow 2 G) (M : Subgroup G) (hTH : (T : Subgroup G) ≤ H)
    (hTV₂ : (T : Subgroup G) ≤ normalizer (V₂ : Set G))
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hTM : (T : Subgroup G) ≤ M) (hLM : L ≤ M) (hHM : ¬ H ≤ M)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      L ⊔ (T : Subgroup G) ≤ N → N = M)
    (V₀ : Subgroup G) [IsElementaryAbelian 2 V₀] (l : G)
    (earlier : EarlierComplement d V₀ l) :
    U = H.pCoreIn 2 ∧ D H U g = conjugate V₁ g ∧
      ((D H U g ⊓ centralizer (L : Set G)).subgroupOf (D H U g)).IsComplement'
        ((conjugate V₁ g).subgroupOf (D H U g)) ∧
      ∃ e : V₀ × ↥(D H U g ⊓ centralizer (L : Set G)) ≃* ↥(D H U g ⊔ V₀),
        ∀ v c, (e (v, c) : G) = (v : G) * (c : G) := by
  have hnorm : ((T.subtype hTH : Sylow 2 H) : Subgroup H) ≤
      normalizer (V₂.subgroupOf H : Set H) := by
    intro t ht
    apply Subgroup.mem_normalizer_iff.mpr
    intro v
    exact Subgroup.mem_normalizer_iff.mp (hTV₂ ht) v.val
  have hrank := d.action.rank_obstruction models (T.subtype hTH)
    (V₂.subgroupOf H) hnorm d.line
  obtain ⟨hlift, _, _, _, _, _, _, hC⟩ :=
    d.source_centralizer_geometry_of_sylow hrank h1442 T M hTH hTL hTM hLM hHM hunique
  have hLI : L ≤ conjugateSpan U L := earlier.span_eq.symm ▸ le_sup_left
  have hLV : L ≤ normalizer (V₀ : Set G) := hLI.trans earlier.span_normalizes
  obtain ⟨hb, hW, hfixed, _⟩ :=
    d.complement_bounds hrank V₀ earlier.frame.plane_le hLV earlier.points
  have hVU : V₀ ≤ rightConjugate U g := by
    have hh : conjugate V₀ g ≤ conjugate U g := map_mono earlier.V_le_U
    rwa [conjugate_eq_self V₀ (hLV d.g_mem_L)] at hh
  have hcenter : rightConjugate U g ⊓ centralizer (rightConjugate U g : Set G) =
      rightConjugate V₁ g := by
    change conjugate U g ⊓ centralizer (conjugate U g : Set G) = conjugate V₁ g
    rw [← center_image, ← conjugate_center, d.center_eq]
  have he (v : G) (hv : v ∈ V₀) : v ^ 2 = 1 :=
    congrArg Subtype.val (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 V₀) ⟨v, hv⟩)
  obtain ⟨_, hcomp, hcollapse, hprod⟩ := source_complement_of_g25 H U V₀ V₁ V₂ L g l
    d.g_mem_L earlier.l_mem earlier.span_eq earlier.span_normalizes he hVU
    (map_mono d.U_le_H) (fun x hx => (hb x hx).1) (fun x hx => (hb x hx).2)
    hW (hfixed l earlier.l_mem) earlier.fixed hcenter earlier.frame
    earlier.U_image earlier.Ug_image earlier.kernel earlier.core_normalizes earlier.core_product
  have hD : D H U g = conjugate V₁ g := hcollapse hC
  have hV₁U : conjugate V₁ g ≤ conjugate U g := map_mono (d.A_le_V₂.trans d.V₂_le_U)
  rw [hD, sup_eq_left.mpr hV₁U] at hlift
  refine ⟨?_, hD, hcomp, hprod⟩
  exact ((Subgroup.map_injective (MulAut.conj g⁻¹).injective) hlift).symm

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore
