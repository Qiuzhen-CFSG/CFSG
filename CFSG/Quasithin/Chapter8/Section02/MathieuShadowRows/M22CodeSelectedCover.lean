module
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.M22CodeSection
public import Theory.Mathieu.M22.CentralCover.QuintetCore
public import Theory.GroupTheory.PerfectCentralCoverPrimeReduction

/-!
# The original marked M₂₂ pair eliminates its central two-core quotient

The literal automizer marking identifies the selected actor with the outer
quintet kernel and the residual with its native affine actor. Transport to
the normalizer of V retains both subgroups and their original intersection
with C(V). Thus the kernel of the actual selected commutator is killed by
every quotient of L/V, and the native double-cover restriction gives a
contradiction. Prime-kernel reduction then removes every nontrivial central
two-core quotient, proving V = O₂(L).

The theorem requires the earlier core commutator and original markings;
the Chapter12 application supplies these on its unchanged selected pair.
Source: Aschbacher--Smith 8.2.10(3), printed p.721, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Sporadic.Mathieu MathieuCode
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows
open ChapterE M22ChapterH.Quintet
variable {G E : Type*} [Group G] [Group E] [Finite E]

/-- The whole original automizer marking and the selected kernel exclude
any compatible central double quotient killing V. All maps are literal. -/
theorem marked_pair_no_central_double_lift
    (V L A R : Subgroup G) (hLV : L ≤ normalizer (V : Set G))
    (hAV : A ≤ normalizer (V : Set G)) (hRL : R ≤ L)
    (hAR : A ≤ normalizer (R : Set G)) (hRA : R ≤ normalizer (A : Set G))
    (hker : A ⊓ centralizer (V : Set G) ≤ V)
    (p : Automizer V →* MathieuCode.m22PairStabilizer) (hp : Function.Injective p)
    (hA : (inducedAutomizer V A).map p = (pCore 2 M22Quintet.Q).map M22Quintet.Q.subtype)
    (q : L →* M22)
    (hq : ∀ l, m22ToPairStabilizer (q l) = p
      (V.normalizerMonoidHom.rangeRestrict (inclusion hLV l)))
    (f : R →* M22Quintet.Q) (hf : f.range = naturalActor)
    (hval : ∀ r, (f r).val = m22ToPairStabilizer (q (inclusion hRL r)))
    (c : PerfectCentralCovering.Cover E M22) (hc : Nat.card c.toMonoidHom.ker = 2)
    (π : L →* E) (hπ : ∀ l, c.toMonoidHom (π l) = q l)
    (hπV : ∀ l : L, (l : G) ∈ V → π l = 1) : False := by
  let N := normalizer (V : Set G)
  let a : N →* MathieuCode.m22PairStabilizer := p.comp V.normalizerMonoidHom.rangeRestrict
  let A0 := A.subgroupOf N
  let R0 := R.subgroupOf N
  have hRN : R ≤ N := hRL.trans hLV
  let e : R0 ≃* R := subgroupOfEquivOfLe hRN
  have hAR0 : A0 ≤ normalizer (R0 : Set N) := by
    rw [←subgroupOf_normalizer_eq hRN]
    exact comap_mono hAR
  have hRA0 : R0 ≤ normalizer (A0 : Set N) := by
    rw [←subgroupOf_normalizer_eq hAV]
    exact comap_mono hRA
  have hA0 : A0.map a = (pCore 2 M22Quintet.Q).map M22Quintet.Q.subtype := by
    rw [←map_map]
    exact hA
  have hR0 : R0.map a = naturalActor.map M22Quintet.Q.subtype := by
    have hrange : R0.map a = (a.comp (inclusion hRN)).range := by
      ext y
      constructor
      · rintro ⟨r,hr,rfl⟩
        exact ⟨⟨r,hr⟩,rfl⟩
      · rintro ⟨r,rfl⟩
        exact ⟨inclusion hRN r,r.property,rfl⟩
    have he : a.comp (inclusion hRN) = M22Quintet.Q.subtype.comp f := by
      apply MonoidHom.ext
      intro r
      exact (hq (inclusion hRL r)).symm.trans (hval r).symm
    rw [hrange,he,MonoidHom.range_comp,hf]
  have hi : Function.Injective m22ToPairStabilizer := by
    intro x y he
    exact m22Embedding_injective (congrArg Subtype.val he)
  have hm (r : R) : q (inclusion hRL r) ∈ nativeActor := by
    have hh : m22ToPairStabilizer (q (inclusion hRL r)) ∈
        nativeActor.map m22ToPairStabilizer := by
      rw [nativeActor_map_pair,←hval]
      exact mem_map_of_mem M22Quintet.Q.subtype (hf ▸ (show f r ∈ f.range from ⟨r,rfl⟩))
    obtain ⟨x,hx,he⟩ := hh
    exact hi he ▸ hx
  let P := nativeActor.comap c.toMonoidHom
  let g : R0 →* P := ((π.comp (inclusion hRL)).comp e.toMonoidHom).codRestrict P
    (fun r => by
      change c.toMonoidHom (π (inclusion hRL (e r))) ∈ nativeActor
      rw [hπ]
      exact hm (e r))
  have hg (r : R0) : m22ToPairStabilizer (c.toMonoidHom (g r).val) = a r.val := by
    change m22ToPairStabilizer (c.toMonoidHom (π (inclusion hRL (e r)))) = a r.val
    rw [hπ,hq]
    rfl
  apply nativeActor_no_selected_commutator_lift A0 R0 hAR0 hRA0 a hA0 hR0 c hc g hg
  intro r hr hz
  have hact : V.normalizerMonoidHom r.val = 1 := by
    have hh : V.normalizerMonoidHom.rangeRestrict r.val = 1 :=
      hp (hz.trans (map_one p).symm)
    exact congrArg Subtype.val hh
  have hrC : ((e r : R) : G) ∈ centralizer (V : Set G) := by
    have hh : r.val ∈ V.normalizerMonoidHom.ker := hact
    rw [V.normalizerMonoidHom_ker] at hh
    exact hh
  apply Subtype.ext
  exact hπV (inclusion hRL (e r)) (hker ⟨hr,hrC⟩)

/-- The original whole-code marking removes the full central two-core
quotient. The selected pair discharges the central double-cover obstruction. -/
theorem marked_pair_core_eq [Finite G]
    (V L A R : Subgroup G) [Group.IsPerfect L]
    (hLV : L ≤ normalizer (V : Set G))
    (hAV : A ≤ normalizer (V : Set G)) (hRL : R ≤ L)
    (hAR : A ≤ normalizer (R : Set G)) (hRA : R ≤ normalizer (A : Set G))
    (hker : A ⊓ centralizer (V : Set G) ≤ V)
    (hVcore : V ≤ L.pCoreIn 2) (hcomm : ⁅L.pCoreIn 2,L⁆ ≤ V)
    (p : Automizer V →* MathieuCode.m22PairStabilizer) (hp : Function.Injective p)
    (hA : (inducedAutomizer V A).map p = (pCore 2 M22Quintet.Q).map M22Quintet.Q.subtype)
    (q : L →* M22) (hqsur : Function.Surjective q) (hqker : q.ker = pCore 2 L)
    (hq : ∀ l, m22ToPairStabilizer (q l) = p
      (V.normalizerMonoidHom.rangeRestrict (inclusion hLV l)))
    (f : R →* M22Quintet.Q) (hf : f.range = naturalActor)
    (hval : ∀ r, (f r).val = m22ToPairStabilizer (q (inclusion hRL r))) :
    V = L.pCoreIn 2 := by
  let W := V.subgroupOf L
  have hVL : V ≤ L := hVcore.trans (pCoreIn_le 2 L)
  let : W.Normal := normal_subgroupOf_of_le_normalizer hLV
  have hWcore : W ≤ pCore 2 L := by
    have hh := comap_mono (f := L.subtype) hVcore
    rw [pCoreIn,comap_map_eq_self_of_injective L.subtype_injective] at hh
    exact hh
  let π := QuotientGroup.mk' W
  let φ := QuotientGroup.lift W q (hWcore.trans hqker.ge)
  have hφsur : Function.Surjective φ :=
    QuotientGroup.lift_surjective_of_surjective W q hqsur _
  have hφker : φ.ker = (pCore 2 L).map π := by
    rw [QuotientGroup.ker_lift,hqker]
  have hφcentral : φ.ker ≤ center (L ⧸ W) := by
    intro x hx
    obtain ⟨l,rfl⟩ := QuotientGroup.mk'_surjective W x
    have hl : l ∈ pCore 2 L := hqker ▸ (show l ∈ q.ker from hx)
    apply mem_center_iff.mpr
    intro y
    obtain ⟨k,rfl⟩ := QuotientGroup.mk'_surjective W y
    apply Eq.symm
    apply commutatorElement_eq_one_iff_mul_comm.mp
    rw [←map_commutatorElement]
    apply (QuotientGroup.eq_one_iff _).mpr
    exact hcomm (commutator_mem_commutator (mem_map_of_mem L.subtype hl) k.property)
  let c : PerfectCentralCovering.Cover (L ⧸ W) M22 := {
    toMonoidHom := φ
    surjective := hφsur
    isPerfect := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective W)
    ker_le_center := hφcentral }
  have htwo : ¬ 2 ∣ Nat.card φ.ker := by
    intro hd
    obtain ⟨D,hDn,hD,hcard⟩ := c.exists_prime_kernel_quotient hd
    let : D.Normal := hDn
    let c' := c.quotientKernelSubgroup D hD
    let θ := (QuotientGroup.mk' D).comp π
    apply marked_pair_no_central_double_lift V L A R hLV hAV hRL hAR hRA hker
      p hp hA q hq f hf hval c' hcard θ
    · intro l
      change (c'.toMonoidHom.comp (QuotientGroup.mk' D)) (π l) = q l
      rw [c.quotientKernelSubgroup_comp D hD]
      rfl
    · intro l hl
      have hπl : π l = 1 := (QuotientGroup.eq_one_iff l).mpr hl
      change QuotientGroup.mk' D (π l) = 1
      rw [hπl,map_one]
  have hφtwo : IsPGroup 2 φ.ker := hφker.symm ▸ pCore_isPGroup.map π
  have hφzero : φ.ker = ⊥ := (eq_bot_iff_card φ.ker).mpr
    (hφtwo.card_eq_or_dvd.resolve_right htwo)
  have hφinj := (MonoidHom.ker_eq_bot_iff φ).mp hφzero
  have heq : pCore 2 L = W := le_antisymm (by
    intro l hl
    apply (QuotientGroup.eq_one_iff l).mp
    apply hφinj
    change q l = φ 1
    rw [MonoidHom.mem_ker.mp (hqker.symm ▸ hl),map_one]) hWcore
  have hm := congrArg (Subgroup.map L.subtype) heq
  rw [map_subgroupOf_eq_of_le hVL] at hm
  exact hm.symm

end CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows
