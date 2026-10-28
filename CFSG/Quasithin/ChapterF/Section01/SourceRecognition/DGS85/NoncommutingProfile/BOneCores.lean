module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.SourceTriple
public import Theory.Frattini.BinarySquares
public import Theory.Frattini.PGroupMap
public import Theory.ElementaryAbelian.Injective

/-!
# The paired core calculation for the noncommuting b=1 branch

The subgroup D is literally the intersection of the two neighbor cores.
Opposite fixed-space generation and the earlier Sylow covers recover Q=ZD.
The opposite center groups centralize D, while Q normalizes it, so the
source actor normalizes D. The two decompositions of the common edge core
identify its Frattini subgroup with both Frattini(D)'s. The whole Borel and
the two local actors normalize this subgroup; faithfulness kills it.
Finally D is elementary and central in its actor, hence lies in an actual
Sylow omega-center. This gives Q=Z at both endpoints.

Only finite vertex stabilizers are required. Neither the completion nor
the graph is assumed finite or a tree. The geometry record lists explicit
intermediate premises: their construction from the marked Chapter 7 natural
modules remains with this Chapter 10 owner. This file does not establish the
full 10.5 alternative, its path parameters, or either b=2 alternative.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
Part II, notation p.153, 10.1(c), 10.4(a,b) and the core clause of 10.5(b),
pp.154--156. The natural-module and Sylow inputs originate in Chapter 7;
the actor supplement and Sylow containment originate in Chapter 6.
-/

@[expose] public noncomputable section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G]

private theorem central_supplement_intersection (A D Z B : Subgroup G)
    (hc : Z ≤ centralizer (D : Set G)) (hA : A = Z ⊔ D) (hDB : D ≤ B) :
    A ⊓ B = (Z ⊓ B) ⊔ D := by
  apply le_antisymm
  · rintro x ⟨hxA,hxB⟩
    have hx : x ∈ (Z : Set G) * (D : Set G) := by
      rw [← coe_mul_of_left_le_normalizer_right Z D
        (hc.trans (Subgroup.centralizer_le_normalizer _)), ← hA]
      exact hxA
    obtain ⟨z,hz,d,hd,rfl⟩ := hx
    have hzB : z ∈ B := by
      simpa only [mul_inv_cancel_right] using B.mul_mem hxB (B.inv_mem (hDB hd))
    exact ((Z ⊓ B) ⊔ D).mul_mem
      ((le_sup_left : Z ⊓ B ≤ (Z ⊓ B) ⊔ D) ⟨hz,hzB⟩)
      ((le_sup_right : D ≤ (Z ⊓ B) ⊔ D) hd)
  · exact sup_le (le_inf (inf_le_left.trans ((le_sup_left : Z ≤ Z ⊔ D).trans hA.ge)) inf_le_right)
      (le_inf ((le_sup_right : D ≤ Z ⊔ D).trans hA.ge) hDB)

private theorem two_central_supplements (A Z B C : Subgroup G)
    (hZA : Z ≤ A) (hc : Z ≤ centralizer (A : Set G))
    (hAB : A ≤ Z ⊔ B) (hAC : A ≤ Z ⊔ C)
    (hnB : Z ≤ normalizer (B : Set G)) (hnC : Z ≤ normalizer (C : Set G))
    (hZ : Z = (Z ⊓ B) ⊔ (Z ⊓ C)) (hBC : B ⊓ C ≤ A) :
    A = Z ⊔ (B ⊓ C) := by
  have hfactor (R : Subgroup G) (hn : Z ≤ normalizer (R : Set G))
      (hAR : A ≤ Z ⊔ R) : A = Z ⊔ (A ⊓ R) := by
    apply le_antisymm
    · intro a ha
      have hx : a ∈ (Z : Set G) * (R : Set G) := by
        rw [← coe_mul_of_left_le_normalizer_right Z R hn]
        exact hAR ha
      obtain ⟨z,hz,r,hr,rfl⟩ := hx
      have hrA : r ∈ A := by
        simpa only [inv_mul_cancel_left] using A.mul_mem (A.inv_mem (hZA hz)) ha
      exact (Z ⊔ (A ⊓ R)).mul_mem
        ((le_sup_left : Z ≤ Z ⊔ (A ⊓ R)) hz)
        ((le_sup_right : A ⊓ R ≤ Z ⊔ (A ⊓ R)) ⟨hrA,hr⟩)
    · exact sup_le hZA inf_le_left
  have hB := hfactor B hnB hAB
  have hC := hfactor C hnC hAC
  have hBA : A = (Z ⊓ C) ⊔ (A ⊓ B) := by
    calc
      A = Z ⊔ (A ⊓ B) := hB
      _ = ((Z ⊓ B) ⊔ (Z ⊓ C)) ⊔ (A ⊓ B) := congrArg (· ⊔ (A ⊓ B)) hZ
      _ = _ := by
        rw [sup_comm (Z ⊓ B), sup_assoc]
        congr 1
        exact sup_eq_right.mpr (le_inf (inf_le_left.trans hZA) inf_le_right)
  have hCI := central_supplement_intersection A (Z ⊓ C) (A ⊓ B) C
    (inf_le_left.trans ((le_centralizer_iff.mp hc).trans (centralizer_le inf_le_left)))
    (hBA.trans (sup_comm _ _)) inf_le_right
  have hABC : (A ⊓ B) ⊓ C = B ⊓ C := by
    rw [inf_assoc, inf_eq_right.mpr hBC]
  rw [hABC] at hCI
  calc
    A = Z ⊔ (A ⊓ C) := hC
    _ = Z ⊔ ((B ⊓ C) ⊔ (Z ⊓ C)) := by rw [hCI]
    _ = Z ⊔ (B ⊓ C) := by
      rw [← sup_assoc, sup_eq_left.mpr (inf_le_left.trans le_sup_left)]

private theorem finite_frattini_central_supplement (A D Z : Subgroup G)
    [Finite A] (hp : IsPGroup 2 A) (he : IsElementaryAbelian 2 Z)
    (hc : Z ≤ centralizer (A : Set G)) (hA : A = Z ⊔ D) :
    (frattini A).map A.subtype = (frattini D).map D.subtype := by
  have hDA : D ≤ A := hA ▸ le_sup_right
  let : Finite D := Finite.of_injective (inclusion hDA) (inclusion_injective _)
  let : Fact (IsPGroup 2 A) := ⟨hp⟩
  let : Fact (IsPGroup 2 D) := ⟨hp.of_injective (inclusion hDA) (inclusion_injective _)⟩
  let : IsElementaryAbelian 2 Z := he
  apply le_antisymm
  · rw [map_le_iff_le_comap, hp.frattini_eq_closure_squares]
    apply (closure_le (K := ((frattini D).map D.subtype).comap A.subtype)).mpr
    rintro _ ⟨a,rfl⟩
    have hx : (a : G) ∈ (Z : Set G) * (D : Set G) := by
      rw [← coe_mul_of_left_le_normalizer_right Z D
        ((hc.trans (centralizer_le hDA)).trans (Subgroup.centralizer_le_normalizer _)), ← hA]
      exact a.property
    obtain ⟨z,hz,d,hd,heq⟩ := hx
    change (a : G) ^ 2 ∈ (frattini D).map D.subtype
    have hcomm : Commute z d := (hc hz d (hDA hd)).symm
    rw [← heq, hcomm.mul_pow, elemPow_eq_one_of_isElementaryAbelian z hz, one_mul]
    exact mem_map_of_mem D.subtype
      (pth_power_mem_frattini_of_isPGroup (p := 2) (⟨d,hd⟩ : D))
  · have hm := map_mono (f := A.subtype)
      (frattini_map_le_of_isPGroup (p := 2) (inclusion hDA))
    simpa only [map_map, subtype_comp_inclusion] using hm

/-- The literal intersection on DGS p.153, with the two neighbors supplied. -/
def D (F : Bool → Subgroup G) (w u : Vertex F) : Subgroup G := Q F w ⊓ Q F u

/-- Both neighbor cores move under the same original graph action. -/
theorem D_translate (F : Bool → Subgroup G) (g : G) (w u : Vertex F) :
    D F (g • w) (g • u) = (D F w u).map (MulAut.conj g).toMonoidHom := by
  rw [D, Q_translate, Q_translate, D,
    Subgroup.map_inf _ _ _ (MulAut.conj g).injective]

private instance finite_Q (F : Bool → Subgroup G) [∀ i, Finite (F i)] (v : Vertex F) :
    Finite (Q F v) :=
  Finite.of_injective (inclusion (Q_le_stabilizer F v)) (inclusion_injective _)

/-- Local inputs to the b=1 calculation. The two core covers come from
7.1(c); the separated cores and the center span are the opposite Sylow and
fixed-space calculations for its natural action. Their construction from
the marked natural module remains part of the Chapter 10 argument. -/
structure OppositeCenterGeometry (F : Bool → Subgroup G) (v w u : Vertex F) where
  adjacent : (graph F).Adj v w
  opposite_adjacent : (graph F).Adj v u
  actor : Subgroup G
  actor_generators : actor = (Z F w ⊔ Z F u) ⊔ Q F v
  supplement : actor ⊔ (stabilizer F v ⊓ stabilizer F w) = stabilizer F v
  sylow : Sylow 2 (stabilizer F v)
  sylow_le_actor : (sylow : Subgroup (stabilizer F v)).map
    (stabilizer F v).subtype ≤ actor
  core_cover : Q F v ≤ Z F v ⊔ Q F w
  opposite_cover : Q F v ≤ Z F v ⊔ Q F u
  center_span : Z F v = (Z F v ⊓ Q F w) ⊔ (Z F v ⊓ Q F u)
  separated : D F w u ≤ Q F v

variable {P : Fin 2 → Subgroup G} {B : Subgroup G}

private theorem core_normalized (F : Bool → Subgroup G) (v : Vertex F) :
    stabilizer F v ≤ normalizer (Q F v : Set G) := by
  simpa only [Q, pCoreIn, normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype]
    using (pCore 2 (stabilizer F v)).le_normalizer_map (stabilizer F v).subtype

private theorem center_properties (h : LocallyRankOneTriple P B)
    (v : Vertex (family P)) :
    Z (family P) v ≤ Q (family P) v ∧
    Z (family P) v ≤ centralizer (Q (family P) v : Set G) ∧
    IsElementaryAbelian 2 (Z (family P) v) := by
  have hz := (source_Z_Q_U h v).1
  exact ⟨fun x hx => ((mem_omegaCenterIn_iff _ _).mp (hz hx)).1,
    fun x hx => ((mem_omegaCenterIn_iff _ _).mp (hz hx)).2.1,
    IsElementaryAbelian.of_injective (inclusion hz) (inclusion_injective _)⟩

private theorem core_normalizes_neighbor (h : LocallyRankOneTriple P B)
    {v w : Vertex (family P)} (hadj : (graph (family P)).Adj v w) :
    Q (family P) v ≤ normalizer (Q (family P) w : Set G) :=
  (source_Z_Q_U h v).2.trans
    (((ballKernel_one_le_edge (family P) hadj).trans inf_le_right).trans
      (core_normalized (family P) w))

/-- Opposite fixed spaces recover Q from Z and the actual neighbor-core intersection. -/
theorem core_eq_center_sup_D (h : LocallyRankOneTriple P B)
    {v w u : Vertex (family P)} (d : OppositeCenterGeometry (family P) v w u) :
    Q (family P) v = Z (family P) v ⊔ D (family P) w u := by
  have hz := center_properties h v
  exact two_central_supplements _ _ _ _ hz.1 hz.2.1
    d.core_cover d.opposite_cover
    (hz.1.trans (core_normalizes_neighbor h d.adjacent))
    (hz.1.trans (core_normalizes_neighbor h d.opposite_adjacent))
    d.center_span d.separated

/-- The source actor normalizes the literal D, using both opposite center groups. -/
theorem actor_normalizes_D (h : LocallyRankOneTriple P B)
    {v w u : Vertex (family P)} (d : OppositeCenterGeometry (family P) v w u) :
    d.actor ≤ normalizer (D (family P) w u : Set G) := by
  rw [d.actor_generators]
  refine sup_le (sup_le ?_ ?_) ?_
  · exact ((center_properties h w).2.1.trans (centralizer_le inf_le_left)).trans
      (Subgroup.centralizer_le_normalizer _)
  · exact ((center_properties h u).2.1.trans (centralizer_le inf_le_right)).trans
      (Subgroup.centralizer_le_normalizer _)
  · exact (le_inf (core_normalizes_neighbor h d.adjacent)
      (core_normalizes_neighbor h d.opposite_adjacent)).trans inf_normalizer_le_normalizer_inf

/-- Normality here is relative to the source local actor. -/
theorem D_normal_in_actor (h : LocallyRankOneTriple P B)
    {v w u : Vertex (family P)} (d : OppositeCenterGeometry (family P) v w u) :
    ((D (family P) w u).subgroupOf d.actor).Normal :=
  normal_subgroupOf_of_le_normalizer (actor_normalizes_D h d)

private theorem elementary_of_frattini_image_bot (A : Subgroup G) [Finite A]
    (hp : IsPGroup 2 A) (hphi : (frattini A).map A.subtype = ⊥) :
    IsElementaryAbelian 2 A := by
  let : Fact (IsPGroup 2 A) := ⟨hp⟩
  exact (frattini_eq_bot_iff_isElementaryAbelian (p := 2)).mp
    ((map_eq_bot_iff_of_injective _ A.subtype_injective).mp hphi)

/-- The two expressions for the edge-core intersection have the same Frattini
subgroup. It is normal in both full endpoints and vanishes by faithfulness.
No finiteness of the completion is used. -/
theorem paired_D_frattini (h : LocallyRankOneTriple P B)
    {u₀ u₁ : Vertex (family P)}
    (d₀ : OppositeCenterGeometry (family P) (base (family P) false)
      (base (family P) true) u₀)
    (d₁ : OppositeCenterGeometry (family P) (base (family P) true)
      (base (family P) false) u₁) :
    (frattini (D (family P) (base (family P) true) u₀)).map
      (D (family P) (base (family P) true) u₀).subtype = ⊥ ∧
    (frattini (D (family P) (base (family P) false) u₁)).map
      (D (family P) (base (family P) false) u₁).subtype = ⊥ := by
  let := finite_endpoints h
  let F := family P
  let a := base F false
  let c := base F true
  let E := Q F a ⊓ Q F c
  let N := (frattini E).map E.subtype
  have local_comparison {v w u : Vertex F} (d : OppositeCenterGeometry F v w u) :
      (frattini (Q F v ⊓ Q F w : Subgroup G)).map (Q F v ⊓ Q F w).subtype =
        (frattini (D F w u)).map (D F w u).subtype := by
    let : Finite (Q F v ⊓ Q F w : Subgroup G) :=
      Finite.of_injective (inclusion (show Q F v ⊓ Q F w ≤ Q F v from inf_le_left))
        (inclusion_injective _)
    have hz := center_properties h v
    have hE := central_supplement_intersection (Q F v) (D F w u) (Z F v) (Q F w)
      (hz.2.1.trans (centralizer_le d.separated)) (core_eq_center_sup_D h d) inf_le_left
    let : IsElementaryAbelian 2 (Z F v) := hz.2.2
    have he : IsElementaryAbelian 2 (Z F v ⊓ Q F w : Subgroup G) :=
      IsElementaryAbelian.of_injective (inclusion inf_le_left) (inclusion_injective _)
    exact finite_frattini_central_supplement _ _ _
      ((isPGroup_pCoreIn 2 (stabilizer F v)).of_injective
        (inclusion inf_le_left) (inclusion_injective _)) he
      (inf_le_left.trans (hz.2.1.trans (centralizer_le inf_le_left))) hE
  have hn₀ : N = (frattini (D F c u₀)).map (D F c u₀).subtype := local_comparison d₀
  have hn₁ : N = (frattini (D F a u₁)).map (D F a u₁).subtype := by
    exact (congrArg (fun K : Subgroup G => (frattini K).map K.subtype)
      (inf_comm (Q F a) (Q F c))).trans (local_comparison d₁)
  have hN : N ≤ B := by
    have hh := (map_subtype_le (frattini E)).trans
      (inf_le_inf (Q_le_stabilizer F a) (Q_le_stabilizer F c))
    simpa only [F, a, c, stabilizer, Subgroup.CosetGeometry.stabilizer_base,
      family, h.intersection] using hh
  have hBN : B ≤ normalizer (N : Set G) := by
    have hBE : B ≤ normalizer (E : Set G) := by
      apply (le_inf ?_ ?_).trans inf_normalizer_le_normalizer_inf
      · apply le_trans _ (core_normalized F a)
        simpa only [F, a, stabilizer, Subgroup.CosetGeometry.stabilizer_base, family]
          using (h.intersection ▸ (inf_le_left : P 0 ⊓ P 1 ≤ P 0))
      · apply le_trans _ (core_normalized F c)
        simpa only [F, c, stabilizer, Subgroup.CosetGeometry.stabilizer_base, family]
          using (h.intersection ▸ (inf_le_right : P 0 ⊓ P 1 ≤ P 1))
    exact hBE.trans (normalizer_le_normalizer_characteristic_image E (frattini E))
  have hp₀ : P 0 ≤ normalizer (N : Set G) := by
    have hl : d₀.actor ≤ normalizer (N : Set G) := by
      rw [hn₀]
      exact (actor_normalizes_D h d₀).trans
        (normalizer_le_normalizer_characteristic_image _ (frattini _))
    have hs : d₀.actor ⊔ B = P 0 := by
      simpa only [stabilizer, Subgroup.CosetGeometry.stabilizer_base, family,
        h.intersection] using d₀.supplement
    rw [← hs]
    exact sup_le hl hBN
  have hp₁ : P 1 ≤ normalizer (N : Set G) := by
    have hl : d₁.actor ≤ normalizer (N : Set G) := by
      rw [hn₁]
      exact (actor_normalizes_D h d₁).trans
        (normalizer_le_normalizer_characteristic_image _ (frattini _))
    have hs : d₁.actor ⊔ B = P 1 := by
      simpa only [stabilizer, Subgroup.CosetGeometry.stabilizer_base, family,
        inf_comm (P 1) (P 0), h.intersection] using d₁.supplement
    rw [← hs]
    exact sup_le hl hBN
  have hn : N.Normal := normalizer_eq_top_iff.mp (top_unique (h.generate ▸ sup_le hp₀ hp₁))
  have hbot := h.faithful N hn hN
  exact ⟨hn₀.symm.trans hbot, hn₁.symm.trans hbot⟩

/-- After the paired Frattini argument, D is central in the same local actor. -/
theorem D_le_actor_center (h : LocallyRankOneTriple P B)
    {v w u : Vertex (family P)} (d : OppositeCenterGeometry (family P) v w u)
    (he : IsElementaryAbelian 2 (D (family P) w u)) :
    D (family P) w u ≤ centerIn d.actor := by
  let F := family P
  let : IsElementaryAbelian 2 (D F w u) := he
  have hz := center_properties h v
  have hDactor : d.actor ≤ centralizer (D F w u : Set G) := by
    rw [d.actor_generators]
    apply sup_le (sup_le
      ((center_properties h w).2.1.trans (centralizer_le inf_le_left))
      ((center_properties h u).2.1.trans (centralizer_le inf_le_right)))
    rw [core_eq_center_sup_D h d]
    exact sup_le (hz.2.1.trans (centralizer_le d.separated))
      (commutator_eq_bot_iff_le_centralizer.mp (commutator_self_eq_bot_iff.mpr inferInstance))
  exact le_inf (d.separated.trans ((le_sup_right : Q F v ≤
    (Z F w ⊔ Z F u) ⊔ Q F v).trans d.actor_generators.ge))
    (le_centralizer_iff.mp hDactor)

private theorem core_eq_center_of_D_elementary (h : LocallyRankOneTriple P B)
    {v w u : Vertex (family P)} (d : OppositeCenterGeometry (family P) v w u)
    (he : IsElementaryAbelian 2 (D (family P) w u)) :
    Q (family P) v = Z (family P) v := by
  let F := family P
  let : IsElementaryAbelian 2 (D F w u) := he
  have hDcentral := (D_le_actor_center h d he).trans inf_le_right
  have hDT : D F w u ≤ (d.sylow : Subgroup (stabilizer F v)).map
      (stabilizer F v).subtype := d.separated.trans (pCoreIn_le_sylow _ d.sylow)
  have hDZ : D F w u ≤ Z F v := by
    apply le_trans _ (le_iSup (fun T : Sylow 2 (stabilizer F v) =>
      omegaCenterIn ((T : Subgroup (stabilizer F v)).map (stabilizer F v).subtype)) d.sylow)
    intro x hx
    apply (mem_omegaCenterIn_iff _ _).mpr
    exact ⟨hDT hx, (hDcentral.trans (centralizer_le d.sylow_le_actor)) hx,
      elemPow_eq_one_of_isElementaryAbelian x hx⟩
  rw [core_eq_center_sup_D h d, sup_eq_left.mpr hDZ]

/-- Structural core clause of 10.5 from the opposite natural-action geometry:
both actual embedded two-cores equal their Sylow-center spans. -/
theorem paired_cores_eq_centers (h : LocallyRankOneTriple P B)
    {u₀ u₁ : Vertex (family P)}
    (d₀ : OppositeCenterGeometry (family P) (base (family P) false)
      (base (family P) true) u₀)
    (d₁ : OppositeCenterGeometry (family P) (base (family P) true)
      (base (family P) false) u₁) :
    Q (family P) (base (family P) false) = Z (family P) (base (family P) false) ∧
    Q (family P) (base (family P) true) = Z (family P) (base (family P) true) := by
  let := finite_endpoints h
  obtain ⟨h₀,h₁⟩ := paired_D_frattini h d₀ d₁
  have hel {v w u : Vertex (family P)} (d : OppositeCenterGeometry (family P) v w u)
      (hphi : (frattini (D (family P) w u)).map (D (family P) w u).subtype = ⊥) :
      IsElementaryAbelian 2 (D (family P) w u) := by
    let : Finite (D (family P) w u) := Finite.of_injective
      (inclusion d.separated) (inclusion_injective _)
    exact elementary_of_frattini_image_bot _
      ((isPGroup_pCoreIn 2 (stabilizer (family P) v)).of_injective
        (inclusion d.separated) (inclusion_injective _)) hphi
  exact ⟨core_eq_center_of_D_elementary h d₀ (hel d₀ h₀),
    core_eq_center_of_D_elementary h d₁ (hel d₁ h₁)⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
