module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.CentralFourAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.ComponentFixedAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.ComponentNaturalResidualAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.ComponentSeedAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.NonsolvableAt.Nonsolvable.ReciprocalSix
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.NormalizerAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ReciprocalSixCenter
public import Theory.Representation.BinaryPermutation.SixCoreResidualCenter
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ReciprocalSix
public import Theory.ElementaryAbelian.EightQuotientRank

/-!
# The reciprocal A₆ radical center and the mixed-pair contradiction: structure at the original group

Let J be the literal cubic residual of a nonfixed augmentation point
centralizer. If E ≤ O₂(J) is central modulo the component's fixed line,
faithfulness on [U,J] puts E in O₂(K). The fixed-space calculation bounds
|E ∩ U| by four, and the perfect central-cover bound gives |E/(E ∩ U)| ≤ 2.
Applied to the preimage of Z(O₂(J)/⟨z⟩), this proves its order is at most four.
This avoids identifying a full extraspecial model and retains central covers.

For the original mixed pair, the existing reciprocal identity identifies
this J with O^{3′}(C_L(z)). Its sixteen-group gives the incompatible lower
bound eight in the SAME quotient. Thus the selected ordinary A₆ branch of
the mixed reciprocal exclusion is proved with the original conjugator and
both radical containments. Earlier-source inputs remain explicit; this does
not assert product reciprocity, point fusion or the final graph argument.
Source: Aschbacher–Smith 13.4.15, printed p.912, refs/quasithin.pdf.

Specialize the original proof to `Structural1222At` at the same G,T.
All action maps, full quotient kernels and source hypotheses are retained;
no universal Chapter12 record is inferred. Intrinsic model and group lemmas
are reused from the preserved source module. This family feeds guarded
nonsolvable-centralizer exclusion on the actual five-dimensional module.

Source: Aschbacher--Smith 13.4.10--17, printed pp.907--915;
see the original `Nonsolvable/ReciprocalSixCenter` proof for the local step.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open LocalGeometry
open Chapter12.Section02 BinaryPermutation Representation.BinaryConjugationCoordinates
open SixCoreResidualMovement SixCoreResidualLine SixCoreResidualCenter
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

open Chapter14.Section03.FaithfulSource Section03.Noncentrality.SupercriticalSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L K V A B : Subgroup G}

theorem original_linear_pair_mixed_commute_of_selected_six_at
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hout : ¬ A ⊔ B ≤ normalizer (L : Set G))
    (hindexL : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexA : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (A : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hres : let X := A ⊔ B
      let Z := omegaOneCenterAmbient (T : Subgroup G)
      let K₁ := (pResidual 2 A).map A.subtype
      let K₂ := (pResidual 2 B).map B.subtype
      let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
      let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
      (primeToResidual 3 C₁).map C₁.subtype = K₁ ∨
        (primeToResidual 3 C₂).map C₂.subtype = K₂)
    (h1332 : Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (hlin : Solvable.LinearAmalgamConclusion T (A ⊔ B))
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hM : normalizer (L : Set G) = L ⊔ (T : Subgroup G))
    (hZV : omegaOneCenterAmbient (T : Subgroup G) ≤ V)
    (W : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6)))
    (hW : Module.finrank (ZMod 2) W = 2)
    (hTW : (T : Subgroup G) ≤ normalizer (m.naturalPreimage W : Set G))
    (hB : B = (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G))
    (hfusion : ∀ v : V, v ≠ 1 → ∀ w ∈ V, IsConj v.val w →
      ∃ n ∈ normalizer (V : Set G), MulAut.conj n v.val = w)
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hAz : A ≤ centralizer ({z.val} : Set G))
    (hK : K ∈ Chapter1.cComponentsIn (centralizer ({z.val} : Set G)))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6))
    :
    let X := A ⊔ B
    let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X
    ∀ g : G, U.conjBy g ≤ B.pCoreIn 2 → V ≤ (B.pCoreIn 2).conjBy g →
      ⁅V,U.conjBy g⁆ = ⊥ := by
  dsimp only
  intro g h₁ h₂
  by_contra hm
  obtain ⟨hfixed,_,_,hU,_,hEQ,_,hc,hn,hlo⟩ := original_linear_pair_mixed_six_center_bounds_at
    h₀ h structural modules D m hTA hTB eA eB hne hout hindexL hindexA hindexB hres
    h1332 fixed hlin eL hM hZV W hW hTW hB hfusion z hzT hzL hAz hK hHN hKM hfK eK
    g h₁ h₂ hm
  let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
  let J := Solvable.firstCentralizerResidual L z.val
  have hz1 : z.val ≠ 1 := fun he => hzL (he ▸ one_mem _)
  obtain ⟨DK,⟨mK⟩,hfix,_,_,_,_⟩ := component_core_marking_of_source_fixed_at
    h₀ h structural m h1332 fixed hindexL z.property hzT hz1 hK.1 hHN hKM hfK hfixed
  have hsplit : conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K = U := by
    have hh := component_seed_split h₀ hzT hz1 hK.1 (h1332 K hfK).1
    rw [component_full_fixed_line_at h structural z.val hz1 hzT hindexL K hK.1 hKM,
      sup_eq_left.mpr (show zpowers z.val ≤ U from hfix.symm ▸ inf_le_left)] at hh
    exact hh
  have hdU : m.constant.val ∈ U := hsplit ▸
    le_conjugateSpanBy _ _ (m.constant_mem_central_four_at h structural).2
  have hdK : m.constant.val ∉ centralizer (K : Set G) := by
    intro hd
    apply hKM
    rw [←fixed_generator_centralizer_at h structural D m
      ⟨m.constant.property,m.constant_fixed⟩
      (fun he => m.constant_ne_one (Subtype.ext he))]
    exact fun k hk => mem_centralizer_singleton_iff.mpr (hd k hk)
  have hrec := component_reciprocal_residual_of_ordinary_six_at h₀ h structural m hzT hz1
    hK hHN (component_quotient_quasisimple h1332 hfK) eK eL
  have hzQ : zpowers z.val ≤ J.pCoreIn 2 := by
    rw [←hc]
    exact (Subgroup.commutator_le_sup _ _).trans (sup_le hEQ le_rfl)
  let : Group.IsPerfect (K.subgroupOf (K ⊔ (T : Subgroup G))) := hfK.1.1.perfect
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe (show K ≤ K ⊔ (T : Subgroup G) from le_sup_left)).toMonoidHom)
    (subgroupOfEquivOfLe (show K ≤ K ⊔ (T : Subgroup G) from le_sup_left)).surjective
  have hupper := core_point_radical_quotient_center_card DK mK eK hU
    ⟨m.constant.val,hdU⟩ hdK z.val hfix (by simpa only [hrec] using hzQ)
  dsimp only at hupper
  rw [hrec] at hupper
  have hhi := hupper hn
  omega
end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
