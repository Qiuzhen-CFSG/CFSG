module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.BinaryRee.RuResidualClass
public import CFSG.Quasithin.ChapterJ.Section03.FiveNormalizer.Local

/-!
# The native five-normalizer symmetry on the first core

The original H-normalizer realizes every automorphism of B₅. Lift its
squaring automorphism and restrict conjugation to Q₀Q₅. This preserves
Q₅ and conjugates the original five-action to its square. The cyclic
fixed subgroup is invariant, so its generator is fixed or inverted.
The theorem retains the pointwise ambient conjugation formula. No order
of the squaring lift or endpoint equivalence is assumed.

Source: Aschbacher–Smith J.3.6 and J.4.4–5, printed pp.439,441–442;
Parrott (1972), pp.672–674, for the semilinear frame application.
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
open Centralizers.Choices
variable {G : Type*} [Group G] [Finite G] (d : LocalSetup G)
  (B5 : Sylow 5 d.toTypeRuSetup.H)

private theorem conj_four_generator (t g:G) (ht:orderOf t=4)
    (hg:g∈normalizer (zpowers t:Set G)) : g*t*g⁻¹=t ∨ g*t*g⁻¹=t⁻¹ := by
  classical
  have ht4:t^4=1:=ht ▸ pow_orderOf_eq_one t
  have hm:g*t*g⁻¹∈zpowers t := (hg t).mp (mem_zpowers t)
  have ho:orderOf (g*t*g⁻¹)=4 := (MulAut.conj g).orderOf_eq t |>.trans ht
  rw [mem_zpowers_iff_mem_range_orderOf,ht] at hm
  obtain ⟨n,hn,he⟩:=Finset.mem_image.mp hm
  have hn4:=Finset.mem_range.mp hn
  interval_cases n
  · simp only [pow_zero] at he
    rw [←he,orderOf_one] at ho
    contradiction
  · exact Or.inl (by simpa only [pow_one] using he.symm)
  · have hh:(g*t*g⁻¹)^2=1:=by rw [←he,←pow_mul]; exact ht4
    have hd:=orderOf_dvd_of_pow_eq_one hh
    rw [ho] at hd
    norm_num at hd
  · apply Or.inr
    rw [←he]
    apply eq_inv_of_mul_eq_one_left
    simpa only [←pow_succ] using ht4

/-- The actual H-normalizer supplies a squaring symmetry of the prescribed
cyclic fixed root. Both the residual and its extension are preserved. -/
theorem exists_firstCore_squaring_action
    (t:fiveHyperplane d B5) (ht:orderOf (t:G)=4)
    (hgen:zpowers (t:G)=fiveHyperplane d B5⊓centralizer (B5Image B5:Set G)) :
    ∃ (ρ:B5Image B5→*MulAut (fiveHyperplane d B5)) (σ:MulAut (fiveHyperplane d B5)),
      (∀a x,(ρ a x:G)=(a:G)*(x:G)*(a:G)⁻¹) ∧
      (∀a,σ*ρ a*σ⁻¹=ρ (a^2)) ∧ (∀a,ρ a t=t) ∧
      (σ t=t ∨ σ t=t⁻¹) ∧
      (∀x,(σ x:G)∈Q₅ d B5 ↔ (x:G)∈Q₅ d B5) := by
  let A:=B5Image B5
  let R:=fiveHyperplane d B5
  have hA:Nat.card A=5:=B5Image_card d.card_Z B5
  let : Fact (Nat.Prime 5):=⟨by decide⟩
  let : IsCyclic A:=isCyclic_of_prime_card hA
  let : CommGroup A:=IsCyclic.commGroup
  let square:MulAut A:={powCoprime (show (Nat.card A).Coprime 2 by rw [hA]; decide) with
    map_mul':=fun x y=>mul_pow x y 2}
  obtain ⟨g,hg⟩:=Section03.local_five_full_ambient_action B5 square
  have hgH : ((g:normalizer (A:Set G)):G)∈d.toTypeRuSetup.H := g.property
  let gG:G:=g
  have hgA:gG∈normalizer (A:Set G):=g.val.property
  have hgsq:∀a∈A,gG*a*gG⁻¹=a^2 := by
    intro a ha
    exact congrArg (fun f:MulAut A=>(f ⟨a,ha⟩:G)) hg
  have hgP:gG∈normalizer (Q₅ d B5:Set G) := by
    rw [mem_normalizer_iff_map_conj_eq,Q₅,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (d.ru2.six.normalized hgH),
      mem_normalizer_iff_map_conj_eq.mp hgA]
  have hgR:gG∈normalizer (R:Set G):=normalizer_inf_normalizer_le_normalizer_sup _ _
    ⟨Q₀_normalized d hgH,hgP⟩
  have hAR:A≤normalizer (R:Set G):=(le_inf
    ((show A≤d.toTypeRuSetup.H from map_subtype_le _).trans (Q₀_normalized d))
    (normalizer_commutator_ge_right _ _)).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  let f:=R.normalizerMonoidHom
  let aN:A→*normalizer (R:Set G):=inclusion hAR
  let gN:normalizer (R:Set G):=⟨gG,hgR⟩
  let ρ:=f.comp aN
  let σ:=f gN
  have htA:(t:G)∈centralizer (A:Set G):=(hgen.le (mem_zpowers (t:G))).2
  have hgroot:gG∈normalizer (zpowers (t:G):Set G):=by
    rw [hgen]
    exact inf_normalizer_le_normalizer_inf ⟨hgR,normalizer_le_normalizer_centralizer A hgA⟩
  refine ⟨ρ,σ,fun _ _=>rfl,?_,?_,?_,?_⟩
  · intro a
    have he:gN*aN a*gN⁻¹=aN (a^2):=Subtype.ext (hgsq a a.property)
    change f gN*f (aN a)*(f gN)⁻¹=f (aN (a^2))
    rw [←map_inv,←map_mul,←map_mul,he]
  · intro a
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mpr (htA a a.property)
  · rcases conj_four_generator (t:G) gG ht hgroot with h|h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  · intro x
    exact ((mem_normalizer_iff.mp hgP) (x:G)).symm

end CFSG.Quasithin.ChapterJ.RuSubgroup
