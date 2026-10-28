module
public import Stellmacher.SectionNine.DistanceOneTerminalResidualGeneration
public import Stellmacher.SectionOne.CThreeCtwoSLTwo

/-!
# Conjugation of the cubic residual modulo the exact Vstar

In the ambient distance-one context, fix an actual order-three element g
of the terminal residual. Every element t of the terminal core satisfies
[t,g]∈Vstar. Every involution s of the terminal stabilizer outside that core
satisfies s*g*s⁻¹*g∈Vstar. These are the two actual conjugation relations
needed to compare factor-swapping actors in the invariant diagonal selection.

The proved residual generation E=Vstar⟨g⟩ first identifies E∩Q with Vstar:
a cyclic order-three subgroup meets the two-core trivially, so decomposing
an element of the intersection leaves only its Vstar factor. Since E and
Q are both terminal-normal, the first commutator belongs to this intersection.
For the second relation, use the actual terminal map onto SL₂(2), whose
kernel is Q. Its outside involution image inverts every cubic element.
This finite identity is checked in the existing three-point permutation
model and transported through the established SL₂(2) equivalence. Thus the
second expression also lies in E∩Q and hence in Vstar.

Source: Stellmacher (9.1), Journal of Algebra190 (1997), p.48, the invariant
diagonal action. All residuals, cores, and quotient maps are the original
ambient ones; the proof introduces no actor-action hypothesis.
-/

namespace Stellmacher.SectionNine
open Stellmacher.Later Stellmacher.SectionsFiveToSeven
open scoped Pointwise
universe u

private theorem sl2_involution_inverts_cubic
    (s g : SL2Two) (hs2 : s ^ 2 = 1) (hsne : s ≠ 1) (hg3 : g ^ 3 = 1) :
    s * g * s⁻¹ * g = 1 := by
  obtain ⟨e⟩ := SectionOne.sl2Two_equiv_perm_three
  have hsmall : ∀ x y : Equiv.Perm (Fin 3),
      x ^ 2 = 1 → x ≠ 1 → y ^ 3 = 1 → x * y * x⁻¹ * y = 1 := by decide +kernel
  have hh := hsmall (e s) (e g) (by rw [← map_pow, hs2, map_one])
    (fun h => hsne (e.injective (by simpa only [map_one] using h)))
    (by rw [← map_pow, hg3, map_one])
  apply e.injective
  simpa only [map_mul, map_inv, map_one] using hh

/-- Core conjugation fixes the cubic residual modulo Vstar, while an
outside terminal involution inverts it. -/
public theorem distance_one_residual_cubic_conjugation_mod_vstar
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hlength : ctx.criticalPath.length = 1)
    (hfaithful : DistanceOneFaithfulConclusion ctx.toLocalContext)
    (hlocal : DistanceOneLocalConclusion ctx.toLocalContext)
    (actor : G) (hactor : actor ∈ EAt ctx.Γ ctx.criticalPath.a')
    (horder : orderOf actor = 3) :
    let V := conjugateClosure
      (ZAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.a')
      (GAt ctx.Γ ctx.criticalPath.a')
    (∀ t ∈ QAt ctx.Γ ctx.criticalPath.a', t * actor * t⁻¹ * actor⁻¹ ∈ V) ∧
    (∀ s ∈ GAt ctx.Γ ctx.criticalPath.a', s ∉ QAt ctx.Γ ctx.criticalPath.a' →
      s ^ 2 = 1 → s * actor * s⁻¹ * actor ∈ V) := by
  classical
  let V := conjugateClosure
    (ZAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.a')
    (GAt ctx.Γ ctx.criticalPath.a')
  let terminal := GAt ctx.Γ ctx.criticalPath.a'
  let Q := QAt ctx.Γ ctx.criticalPath.a'
  let E := EAt ctx.Γ ctx.criticalPath.a'
  have hEV : E ≤ terminal := by
    simpa only [E, terminal, EAt, CosetGraphContext.e, ctx.Γ.twoResidualAt_def,
      GAt, CosetGraphContext.stabilizer] using SevenSix.twoResidualIn_le terminal
  have hEn : terminal ≤ Subgroup.normalizer (E : Set G) := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hEV).mp
    simpa only [E, terminal, EAt, CosetGraphContext.e, ctx.Γ.twoResidualAt_def,
      GAt, CosetGraphContext.stabilizer] using SevenSix.twoResidualIn_normal terminal
  have hQT : Q ≤ terminal := by
    simpa only [Q, terminal, QAt, CosetGraphContext.q, ctx.Γ.twoCoreAt_def,
      GAt, CosetGraphContext.stabilizer] using SevenSix.twoCoreIn_le terminal
  have hQn : terminal ≤ Subgroup.normalizer (Q : Set G) := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hQT).mp
    simpa only [Q, terminal, QAt, CosetGraphContext.q, ctx.Γ.twoCoreAt_def,
      GAt, CosetGraphContext.stabilizer] using SevenSix.twoCoreIn_normal terminal
  have hQp : IsPGroup 2 Q := by
    change IsPGroup 2 (ctx.Γ.twoCoreAt ctx.criticalPath.a')
    rw [ctx.Γ.twoCoreAt_def]
    exact (pCore_isPGroup (p := 2) (G := terminal)).map terminal.subtype
  have hcontain := distance_one_vstar_containments ctx.toLocalContext hlength
  have hVT : V ≤ terminal := hcontain.1.1
  have hVQ : V ≤ Q := hcontain.2.1
  have hVn : terminal ≤ Subgroup.normalizer (V : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVT).mp hcontain.1.2
  let C := Subgroup.zpowers actor
  have hCE : C ≤ E := Subgroup.zpowers_le.mpr hactor
  have hCcard : Nat.card C = 3 := by rw [Nat.card_zpowers, horder]
  have hCp : IsPGroup 3 C := IsPGroup.of_card (n := 1) hCcard
  have hd : Disjoint C Q := hCp.disjoint_of_coprime hQp (by decide)
  have hgen : E = V ⊔ C :=
    distance_one_terminal_residual_eq_vstar_sup_zpowers ctx hlength hfaithful hlocal actor hactor horder
  have hEQV : E ⊓ Q ≤ V := by
    intro x hx
    have hprod : x ∈ (↑(V ⊔ C) : Set G) := hgen ▸ hx.1
    rw [Subgroup.coe_mul_of_right_le_normalizer_left V C (hCE.trans (hEV.trans hVn))] at hprod
    obtain ⟨v, hv, c, hc, heq⟩ := hprod
    change v * c = x at heq
    have hcQ : c ∈ Q := by
      have hh : v * c ∈ Q := by rw [heq]; exact hx.2
      exact (Q.mul_mem_cancel_left (hVQ hv)).mp hh
    have hcone : c = 1 := Subgroup.disjoint_def.mp hd hc hcQ
    rw [hcone, mul_one] at heq
    exact heq ▸ hv
  have hactorT : actor ∈ terminal := hEV hactor
  have hpow : actor ^ 3 = 1 := by rw [← horder]; exact pow_orderOf_eq_one actor
  constructor
  · intro t ht
    apply hEQV
    constructor
    · exact E.mul_mem ((Subgroup.mem_normalizer_iff.mp (hEn (hQT ht)) actor).mp hactor)
        (E.inv_mem hactor)
    · change t * actor * t⁻¹ * actor⁻¹ ∈ Q
      have hh : actor * t⁻¹ * actor⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.mp (hQn hactorT) t⁻¹).mp (Q.inv_mem ht)
      simpa only [mul_assoc] using Q.mul_mem ht hh
  · intro s hs hsout hs2
    apply hEQV
    constructor
    · exact E.mul_mem ((Subgroup.mem_normalizer_iff.mp (hEn hs) actor).mp hactor) hactor
    · obtain ⟨projection, hsurj, hker⟩ := hlocal.2.1
      change terminal →* SL2Two at projection
      change projection.ker = Q.subgroupOf terminal at hker
      let sn : terminal := ⟨s, hs⟩
      let an : terminal := ⟨actor, hactorT⟩
      have hsne : projection sn ≠ 1 := by
        intro hh
        have hmem : sn ∈ projection.ker := MonoidHom.mem_ker.mpr hh
        rw [hker] at hmem
        exact hsout hmem
      have hsn2 : sn ^ 2 = 1 := Subtype.ext hs2
      have han3 : an ^ 3 = 1 := Subtype.ext hpow
      have hquot := sl2_involution_inverts_cubic (projection sn) (projection an)
        (by rw [← map_pow, hsn2, map_one]) hsne (by rw [← map_pow, han3, map_one])
      have hmem : sn * an * sn⁻¹ * an ∈ projection.ker := by
        apply MonoidHom.mem_ker.mpr
        simpa only [map_mul, map_inv] using hquot
      rw [hker] at hmem
      exact hmem

end Stellmacher.SectionNine
