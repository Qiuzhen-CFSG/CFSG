module
public import CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic.ReducedMarking.CubicBaumann
public import CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic.ReducedMarking.SylowMarking
/-!
# Constructing the reduced A₃ setup

The actual KT action has full binary special-linear image and the reduced
Baumann image is the Sylow image. Restriction therefore keeps the full
image on K Baum(T). Marking that Sylow and the module simultaneously gives
the upper-root parameter and literal coordinates required by Setup.
The A₃ core and centralizer identities follow from actual Sylow placement.

Source: Aschbacher–Smith C.5.4(2),(4), printed p.155.
-/
public section
open Subgroup
namespace CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic.ReducedMarking
open ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G] {R K : Subgroup G} {F : Type*} [Field F]

theorem exists_cubic_reduced_setup (h : Setup R K F) (hA : IsAlternatingBlock K 3)
    (T : Subgroup G) (hT : IsPGroup 2 T) (hn : T ≤ normalizer (K : Set G)) (hST : S R ≤ T)
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (hmin : ChapterB.IsMinimalParabolicOver P ⊤)
    (hno : ∀ N : Subgroup G, N ≤ T → normalizer (T : Set G) ≤ normalizer (N : Set G) →
      K ⊔ T ≤ normalizer (N : Set G) → N = ⊥) :
    Nonempty (Setup T K (ZMod 2)) := by
  obtain ⟨e,q,hq,hker,he,himage,hsyl⟩ := cubic_reduced_action_and_sylow h hA T hT hn hST P hP hmin hno
  let A := K ⊔ T
  let B := K ⊔ S T
  have hBA : B ≤ A := sup_le_sup_left (show S T ≤ T from inf_le_left) K
  let q₀ := q.comp (inclusion hBA)
  have hgen : K.subgroupOf A ⊔ (S T).subgroupOf A = B.subgroupOf A :=
    (subgroupOf_sup le_sup_left (inf_le_left.trans le_sup_right)).symm
  have hfull : (B.subgroupOf A).map q = ⊤ := by
    rw [← hgen,Subgroup.map_sup,himage,← Subgroup.map_sup,
      ← subgroupOf_sup (show K ≤ A from le_sup_left) (show T ≤ A from le_sup_right),
      subgroupOf_self,map_top_of_surjective _ hq]
  have hq₀ : Function.Surjective q₀ := by
    intro z
    obtain ⟨v,hv,hvz⟩ := (hfull.symm ▸ mem_top z : z ∈ (B.subgroupOf A).map q)
    exact ⟨⟨v,hv⟩,hvz⟩
  have hq₀ker : q₀.ker = (centralizer (U K : Set G)).subgroupOf B := by
    ext z
    change inclusion hBA z ∈ q.ker ↔ _
    rw [hker]
    rfl
  have hπker (u : U K) : e.toMonoidHom u = 1 ↔ (u : G) ∈ centralizer (K : Set G) := by
    change e u = 1 ↔ _
    rw [e.map_eq_one_iff]
    exact ⟨fun he => he ▸ (centralizer (K : Set G)).one_mem,cubic_module_fixed_eq_one hA u⟩
  obtain ⟨q₁,π,hq₁,hπ,hker₁,hπker₁,himage₁,he₁⟩ := marked_sylow_quotient K T (inf_le_left.trans hn)
    cubicNaturalAction q₀ e.toMonoidHom hq₀ e.surjective hq₀ker hπker
    (fun z u => he (inclusion hBA z) u) hsyl
  exact setup_of_natural_quotient K T (Or.inr hA) (inf_le_left.trans hn) hsyl
    cubicNaturalAction (fun _ _ => rfl) q₁ π hq₁ hπ hker₁ hπker₁ himage₁ (Or.inr hA) he₁
end CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic.ReducedMarking
