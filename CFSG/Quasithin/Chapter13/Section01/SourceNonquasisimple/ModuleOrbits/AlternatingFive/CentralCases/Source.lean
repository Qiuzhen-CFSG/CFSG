module
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.AlternatingFive.Stabilizer
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.AlternatingFive.CentralCases.OrbitSums


/-!
# The small-kernel and inner-action exclusions in original 13.1.12

The orbit-sum argument supplies a component translate fixed by T whenever
T fixes the central kernel. Pulling back that fixed translate along an element
of L puts an ambient Sylow in the literal C_{N_G(L)}(u). The stipulated local
Sylow selection then implies C_T(u)=T by cardinality comparison.

For central binary rank at most one, all actors fix the kernel. For inner
natural quotient action, uniqueness on the generated cover proves innerness
of the full action and hence fixes its kernel. The original `Marking.sourceCover`
discharges full movement in both source applications. Their final corollary
supplies central rank two and a genuine outer natural actor to the remaining
six-space branch, without assuming its orbit or stabilizer conclusions.

Source: Aschbacher--Smith, original Lemma 13.1.12, printed p.872/PDF p.889.
The conclusions hold also for u=1, so no nonidentity premise is needed here.
-/

public noncomputable section

open Subgroup Representation Representation.OneCohomology Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.AlternatingFive
open Chapter1 Chapter1.Section02 Chapter12.Section02
open Representation.SL2FourNatural
namespace Marking
variable {G W : Type*} [Group G] [Finite G] [AddCommGroup W] [Module (ZMod 2) W]
  {T : Sylow 2 G} {L : Subgroup G} (d : Marking T L W)

omit [Finite G] in
private theorem actor_fixes_iff (a : (L ⊔ (T : Subgroup G) : Subgroup G))
    (u : normalizerMoved L) :
    d.actor a (d.coordinates u).toAdd = (d.coordinates u).toAdd ↔
      (a : G) ∈ centralizer ({(u : G)} : Set G) := by
  rw [← d.equivariant]
  constructor
  · intro h
    have hu := congrArg Subtype.val (d.coordinates.injective h)
    change (a : G) * (u : G) * (a : G)⁻¹ = (u : G) at hu
    exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hu)
  · intro h
    apply congrArg (fun x => (d.coordinates x).toAdd)
    apply Subtype.ext
    change (a : G) * (u : G) * (a : G)⁻¹ = (u : G)
    rw [mem_centralizer_singleton_iff.mp h, mul_inv_cancel_right]

/-- A fixed central kernel makes every locally Sylow-selected vector two-central.
Full movement is the explicit generic premise, supplied below by the source. -/
theorem centralizes_of_kernel_fixed
    (hmoved : ⁅normalizerMoved L,L⁆ = normalizerMoved L)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hfix : ∀ (t : T) z, z ∈ d.projection.toLinearMap.ker →
      d.actor (inclusion le_sup_right t) z = z)
    (u : normalizerMoved L)
    (hlocal : IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({(u : G)} : Set G))
      (normalizer (L : Set G) ⊓ centralizer ({(u : G)} : Set G))) :
    (T : Subgroup G) ≤ centralizer ({(u : G)} : Set G) := by
  let c : NaturalCover T W :=
    { component := d.representation
      projection := d.projection
      cover := (d.naturalCover hmoved).cover
      actor := d.actor.comp (inclusion le_sup_right)
      conjugation := d.conjugation.comp (inclusion le_sup_right)
      naturalActor := d.naturalActor.comp (inclusion le_sup_right)
      compatible := fun t => d.compatible (inclusion le_sup_right t)
      quotient_action := fun t => d.quotient_action (inclusion le_sup_right t) }
  obtain ⟨l,hl⟩ := c.exists_fixed_component_translate T.isPGroup' hfix (d.coordinates u).toAdd
  obtain ⟨l,rfl⟩ := d.onto l
  let v := componentAction L l u
  have hv : (d.coordinates v).toAdd = d.representation (d.component l) (d.coordinates u).toAdd :=
    (d.equivariant (inclusion le_sup_left l) u).trans (d.component_action l _)
  have htfix : (T : Subgroup G) ≤ centralizer ({(v : G)} : Set G) := by
    intro t ht
    apply (d.actor_fixes_iff (inclusion le_sup_right ⟨t,ht⟩) v).mp
    rw [hv]
    exact hl ⟨t,ht⟩
  let R : Sylow 2 G := T.mapSurjective (f := (MulAut.conj (l : G)⁻¹).toMonoidHom)
    (MulAut.conj (l : G)⁻¹).surjective
  let M : Subgroup G := normalizer (L : Set G) ⊓ centralizer ({(u : G)} : Set G)
  have hRM : (R : Subgroup G) ≤ M := by
    rintro _ ⟨t,ht,rfl⟩
    constructor
    · exact (normalizer (L : Set G)).mul_mem
        ((normalizer (L : Set G)).mul_mem
          ((normalizer (L : Set G)).inv_mem (L.le_normalizer l.property)) (hTL ht))
        (by simpa using L.le_normalizer l.property)
    · have hh := mem_centralizer_singleton_iff.mp (htfix ht)
      change t * ((l : G) * (u : G) * (l : G)⁻¹) =
        ((l : G) * (u : G) * (l : G)⁻¹) * t at hh
      apply mem_centralizer_singleton_iff.mpr
      change ((l : G)⁻¹ * t * ((l : G)⁻¹)⁻¹) * (u : G) =
        (u : G) * ((l : G)⁻¹ * t * ((l : G)⁻¹)⁻¹)
      have he := congrArg (fun x : G => (l : G)⁻¹ * x * (l : G)) hh
      simpa [mul_assoc] using he
  obtain ⟨P,hP⟩ := hlocal
  have hc : Nat.card ↥((T : Subgroup G) ⊓ centralizer ({(u : G)} : Set G)) = Nat.card T := by
    rw [← hP, card_map_of_injective M.subtype_injective]
    calc
      Nat.card P = Nat.card (R.subtype hRM) := Nat.card_congr (P.equiv (R.subtype hRM)).toEquiv
      _ = Nat.card R := Nat.card_congr (subgroupOfEquivOfLe hRM).toEquiv
      _ = Nat.card T := Nat.card_congr (R.equiv T).toEquiv
  exact inf_eq_left.mp (eq_of_le_of_card_ge inf_le_left hc.ge)

/-- The actual natural T-action being inner forces its full-cover lift to be inner,
so the selected vector is centralized by T. -/
theorem centralizes_of_inner_natural
    (hmoved : ⁅normalizerMoved L,L⁆ = normalizerMoved L)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hinner : ∀ t : T, ∃ l : SL, ∀ v,
      d.naturalActor (inclusion le_sup_right t) v = Natural l v)
    (u : normalizerMoved L)
    (hlocal : IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({(u : G)} : Set G))
      (normalizer (L : Set G) ⊓ centralizer ({(u : G)} : Set G))) :
    (T : Subgroup G) ≤ centralizer ({(u : G)} : Set G) := by
  apply d.centralizes_of_kernel_fixed hmoved hTL _ u hlocal
  intro t z hz
  obtain ⟨l,hl⟩ := hinner t
  have he := (d.naturalCover hmoved).actor_eq_component_of_natural
    (inclusion le_sup_right t) l hl z
  exact he.trans (d.kernel_fixed hz l)

/-- The small binary kernel exclusion, including zero-dimensional kernels. -/
theorem centralizes_of_small_kernel
    (hmoved : ⁅normalizerMoved L,L⁆ = normalizerMoved L)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hd : Module.finrank (ZMod 2) d.projection.toLinearMap.ker ≤ 1)
    (u : normalizerMoved L)
    (hlocal : IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({(u : G)} : Set G))
      (normalizer (L : Set G) ⊓ centralizer ({(u : G)} : Set G))) :
    (T : Subgroup G) ≤ centralizer ({(u : G)} : Set G) := by
  let : Finite W := Finite.of_equiv (normalizerMoved L) d.coordinates.toEquiv
  apply d.centralizes_of_kernel_fixed hmoved hTL _ u hlocal
  exact fun t z hz => (d.naturalCover hmoved).kernel_fixed_of_finrank_le_one hd
    (inclusion le_sup_right t) z hz


/-- The original U in 13.1.12: a kernel of binary rank at most one makes
every locally selected vector central in T. -/
theorem source_centralizes_of_small_kernel
    (h : Hypothesis1311 T) (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L))
    (hd : Module.finrank (ZMod 2) d.projection.toLinearMap.ker ≤ 1)
    (u : normalizerMoved L)
    (hlocal : IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({(u : G)} : Set G))
      (normalizer (L : Set G) ⊓ centralizer ({(u : G)} : Set G))) :
    (T : Subgroup G) ≤ centralizer ({(u : G)} : Set G) := by
  let : Finite W := Finite.of_equiv (normalizerMoved L) d.coordinates.toEquiv
  have hTL := radicalLocal_invariant_source hL.1.1
    (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hn
  have hm := (normalizerMoved_commutator_and_card hL.1.1
    (faithful_maximal_normalizer_moved h.simpleQTKE hL hTL).2.1).1
  apply d.centralizes_of_kernel_fixed hm hTL _ u hlocal
  exact fun t z hz => (d.sourceCover h hL hn).kernel_fixed_of_finrank_le_one hd
    (inclusion le_sup_right t) z hz

/-- The original U in 13.1.12: innerness on the natural quotient suffices;
uniqueness derives the full-cover action, including its central kernel. -/
theorem source_centralizes_of_inner_natural
    (h : Hypothesis1311 T) (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L))
    (hinner : ∀ t : T, ∃ l : SL, ∀ v,
      d.naturalActor (inclusion le_sup_right t) v = Natural l v)
    (u : normalizerMoved L)
    (hlocal : IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({(u : G)} : Set G))
      (normalizer (L : Set G) ⊓ centralizer ({(u : G)} : Set G))) :
    (T : Subgroup G) ≤ centralizer ({(u : G)} : Set G) := by
  have hTL := radicalLocal_invariant_source hL.1.1
    (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hn
  have hm := (normalizerMoved_commutator_and_card hL.1.1
    (faithful_maximal_normalizer_moved h.simpleQTKE hL hTL).2.1).1
  apply d.centralizes_of_kernel_fixed hm hTL _ u hlocal
  intro t z hz
  obtain ⟨l,hl⟩ := hinner t
  have he := (d.sourceCover h hL hn).actor_eq_component_of_natural
    (inclusion le_sup_right t) l hl z
  exact he.trans (d.kernel_fixed hz l)


/-- The exclusions give exactly the inputs needed by the remaining outer
six-space branch: central rank two and a genuinely outer natural T-actor. -/
theorem source_kernel_rank_two_and_outer
    (h : Hypothesis1311 T) (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) (u : normalizerMoved L)
    (hlocal : IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({(u : G)} : Set G))
      (normalizer (L : Set G) ⊓ centralizer ({(u : G)} : Set G)))
    (hm : ¬ (T : Subgroup G) ≤ centralizer ({(u : G)} : Set G)) :
    Module.finrank (ZMod 2) d.projection.toLinearMap.ker = 2 ∧
      ∃ t : T, ¬ ∃ l : SL, ∀ v,
        d.naturalActor (inclusion le_sup_right t) v = Natural l v := by
  classical
  let : Finite W := Finite.of_equiv (normalizerMoved L) d.coordinates.toEquiv
  constructor
  · have hlo : ¬ Module.finrank (ZMod 2) d.projection.toLinearMap.ker ≤ 1 :=
      fun hd => hm (d.source_centralizes_of_small_kernel h hL hn hd u hlocal)
    have hhi := (d.sourceCover h hL hn).kernel_finrank_le_two
    change Module.finrank (ZMod 2) d.projection.toLinearMap.ker ≤ 2 at hhi
    omega
  · by_contra! hi
    exact hm (d.source_centralizes_of_inner_natural h hL hn hi u hlocal)

end Marking
end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.AlternatingFive
