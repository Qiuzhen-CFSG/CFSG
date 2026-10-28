module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.Models
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.Geometry
public import Theory.SpecificGroups.PSL3Two.Parabolics.CompatibleMarking

/-!
# Geometry of the L₃(2) marking in 13.6.22

The actual invariant four-group l satisfies l=[l,D]. Its image in U/C_U(K)
cannot be fixed by D: otherwise this commutator identity puts l in C_U(K),
forcing l=1. The point parabolic fixes every invariant subgroup of size at most
four on a natural or doubled-natural module. After marking the Sylow subgroup
by inner conjugation, the actual parabolic is consequently the line parabolic.
Relative normality and a two-group quotient place its residual in D's image.

The remaining source realization must construct the models and the parabolic
hypotheses from C.1.32/34 and the original local setup, and must establish the
separate checked-center commutator identity. No completion of 13.6.22 is
asserted here.

Source: Aschbacher--Smith, combined 1 March 2004 manuscript, pp.932--933.
-/

@[expose] public section
open Subgroup Representation BinaryLinearThree
open Matrix.PSL3Two Matrix.PSL3Two.MarkedAutomorphisms
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.A5Module
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch
variable {G V : Type*} [_root_.Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {K U D P l : Subgroup G} {ρ : Representation (ZMod 2) BinaryLinearThree.Group V}

theorem line_image_invariant (m : ConjugationQuotientModel K U ρ)
    (hn : P ≤ normalizer (l : Set G))
    (g : (P.subgroupOf K).map m.actor)
    (x : (l.subgroupOf U).map m.quotient) :
    Multiplicative.ofAdd (ρ g (Multiplicative.toAdd (x : Multiplicative V))) ∈
      (l.subgroupOf U).map m.quotient := by
  obtain ⟨k, hk, hg⟩ := g.property
  obtain ⟨u, hu, hx⟩ := x.property
  rw [← hg, ← hx, ← m.equivariant]
  apply mem_map_of_mem
  change (k : G) * (u : G) * (k : G)⁻¹ ∈ l
  exact (mem_normalizer_iff.mp (hn hk) u).mp hu

theorem line_eq_bot_of_image_fixed (m : ConjugationQuotientModel K U ρ)
    (hDK : D ≤ K) (hlU : l ≤ U) (hl : ⁅l, D⁆ = l)
    (hf : ∀ d : D, ∀ x : l,
      ρ (m.actor ⟨d, hDK d.property⟩)
        (Multiplicative.toAdd (m.quotient ⟨x, hlU x.property⟩)) =
        Multiplicative.toAdd (m.quotient ⟨x, hlU x.property⟩)) : l = ⊥ := by
  have hcomm : ⁅D, l⁆ ≤ m.quotient.ker.map U.subtype := by
    apply commutator_le.mpr
    intro d hd x hx
    let u : U := ⟨x, hlU hx⟩
    let k : K := ⟨d, hDK hd⟩
    let c := U.normalizerMonoidHom ⟨k, m.normalizes k.property⟩ u
    have he : m.quotient c = m.quotient u := by
      apply Multiplicative.toAdd.injective
      rw [m.equivariant]
      exact hf ⟨d, hd⟩ ⟨x, hx⟩
    have hm : c * u⁻¹ ∈ m.quotient.ker := by
      change m.quotient (c * u⁻¹) = 1
      rw [map_mul, map_inv, he, mul_inv_cancel]
    exact ⟨c * u⁻¹, hm, rfl⟩
  have hk : l ≤ centralizer (K : Set G) := by
    rw [commutator_comm, hl] at hcomm
    intro x hx
    obtain ⟨u, hu, rfl⟩ := hcomm hx
    rw [m.kernel] at hu
    exact hu
  rw [← hl]
  exact commutator_eq_bot_iff_le_centralizer.mpr (hk.trans (centralizer_le hDK))

theorem point_image_impossible [Finite G] [Finite V]
    (m : ConjugationQuotientModel K U ρ)
    (hDK : D ≤ K) (hDP : D ≤ P)
    (hlU : l ≤ U) (hl : ⁅l, D⁆ = l) (hcard : Nat.card l = 4)
    (hn : P ≤ normalizer (l : Set G))
    (hsmall : ∀ H : Subgroup (Multiplicative V), Nat.card H ≤ 4 →
      (∀ g : pointParabolicSL, ∀ x : H,
        Multiplicative.ofAdd (ρ g (Multiplicative.toAdd (x : Multiplicative V))) ∈ H) →
      ∀ g : pointParabolicSL, ∀ x : H,
        ρ g (Multiplicative.toAdd (x : Multiplicative V)) =
          Multiplicative.toAdd (x : Multiplicative V)) :
    (P.subgroupOf K).map m.actor ≠ pointParabolicSL := by
  intro heq
  let H := (l.subgroupOf U).map m.quotient
  have hc : Nat.card H ≤ 4 := by
    have hsurj : Function.Surjective
        (fun x : l => (⟨m.quotient ⟨x, hlU x.property⟩,
          mem_map_of_mem m.quotient x.property⟩ : H)) := by
      rintro ⟨y, u, hu, rfl⟩
      exact ⟨⟨u, hu⟩, rfl⟩
    simpa only [hcard] using Nat.card_le_card_of_surjective _ hsurj
  have hinv : ∀ g : pointParabolicSL, ∀ x : H,
      Multiplicative.ofAdd (ρ g (Multiplicative.toAdd (x : Multiplicative V))) ∈ H := by
    intro g x
    exact line_image_invariant m hn ⟨g, heq.symm ▸ g.property⟩ x
  have hbot := line_eq_bot_of_image_fixed m hDK hlU hl (fun d x => by
    apply hsmall H hc hinv
      ⟨m.actor ⟨d, hDK d.property⟩, heq ▸ mem_map_of_mem m.actor (hDP d.property)⟩
      ⟨m.quotient ⟨x, hlU x.property⟩, mem_map_of_mem m.quotient x.property⟩)
  have hc' := (eq_bot_iff_card l).mp hbot
  omega
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch
open Subgroup Representation BinaryLinearThree
open Matrix.PSL3Two Matrix.PSL3Two.MarkedAutomorphisms
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.A5Module
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch
open scoped Pointwise
variable {G V : Type*} [_root_.Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {K U D P l : Subgroup G} {ρ : Representation (ZMod 2) BinaryLinearThree.Group V}

private theorem inner_sylow_marking (S : Sylow 2 BinaryLinearThree.Group) :
    ∃ g : BinaryLinearThree.Group,
      (S : Subgroup BinaryLinearThree.Group).map (MulAut.conj g).toMonoidHom = borelSL := by
  let S₀ : Sylow 2 BinaryLinearThree.Group := Sylow.ofCard borelSL (by
    rw [card_borelSL, card_SL]
    decide +kernel)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq BinaryLinearThree.Group S S₀
  refine ⟨g, ?_⟩
  change ((g • S : Sylow 2 BinaryLinearThree.Group) : Subgroup BinaryLinearThree.Group) = _
  rw [hg]
  rfl

theorem image_residual_le (f : K →* BinaryLinearThree.Group)
    (hPK : P ≤ K) (hn : (D.subgroupOf P).Normal)
    (hq : letI := hn; IsPGroup 2 (P ⧸ D.subgroupOf P)) :
    residual ((P.subgroupOf K).map f) ≤ (D.subgroupOf K).map f := by
  let _ := hn
  let q : P →* (P.subgroupOf K).map f :=
    { toFun p := ⟨f ⟨p, hPK p.property⟩, mem_map_of_mem f p.property⟩
      map_one' := Subtype.ext (map_one f)
      map_mul' a b := by
        apply Subtype.ext
        exact map_mul f (⟨a, hPK a.property⟩ : K) (⟨b, hPK b.property⟩ : K) }
  have hsurj : Function.Surjective q := by
    rintro ⟨y, k, hk, rfl⟩
    exact ⟨⟨k, hk⟩, rfl⟩
  have hres : pResidual 2 P ≤ D.subgroupOf P := sInf_le ⟨hn, hq⟩
  have himage := map_mono (f := q) hres
  rw [map_pResidual_of_surjective 2 q hsurj] at himage
  rintro y ⟨x, hx, rfl⟩
  obtain ⟨p, hp, he⟩ := himage hx
  refine ⟨⟨p, hPK p.property⟩, hp, ?_⟩
  exact congrArg Subtype.val he

theorem exists_geometric_marking (m : ConjugationQuotientModel K U ρ)
    (hPK : P ≤ K) (hDP : D ≤ P)
    (hlU : l ≤ U) (hl : ⁅l, D⁆ = l) (hcard : Nat.card l = 4)
    (hn : P ≤ normalizer (l : Set G))
    (S : Sylow 2 BinaryLinearThree.Group)
    (hS : (S : Subgroup BinaryLinearThree.Group) ≤ (P.subgroupOf K).map m.actor)
    (hproper : (P.subgroupOf K).map m.actor ≠ ⊤)
    (htwo : ¬ IsPGroup 2 ((P.subgroupOf K).map m.actor))
    (hsmall : ∀ H : Subgroup (Multiplicative V), Nat.card H ≤ 4 →
      (∀ g : pointParabolicSL, ∀ x : H,
        Multiplicative.ofAdd (ρ g (Multiplicative.toAdd (x : Multiplicative V))) ∈ H) →
      ∀ g : pointParabolicSL, ∀ x : H,
        ρ g (Multiplicative.toAdd (x : Multiplicative V)) =
          Multiplicative.toAdd (x : Multiplicative V)) :
    ∃ g : BinaryLinearThree.Group,
      (P.subgroupOf K).map (conjugate m g).actor = lineParabolicSL := by
  obtain ⟨g, hg⟩ := inner_sylow_marking S
  let E := (MulAut.conj g).mapSubgroup
  let H := (P.subgroupOf K).map m.actor
  have he : (P.subgroupOf K).map (conjugate m g).actor = E H := by
    change (P.subgroupOf K).map ((MulAut.conj g).toMonoidHom.comp m.actor) = _
    exact (map_map _ _ _).symm
  have hB : borelSL ≤ E H := by
    rw [← hg]
    exact E.monotone hS
  have hP : E H ≠ ⊤ := by
    intro ht
    apply hproper
    exact E.injective (ht.trans E.map_top.symm)
  have h₂ : ¬ IsPGroup 2 (E H) := by
    intro hh
    exact htwo (hh.of_equiv ((MulAut.conj g).subgroupMap H).symm)
  rcases parabolic_of_borel_le_of_not_two (E H) hB hP h₂ with hp | hp
  · exact (point_image_impossible (conjugate m g) (hDP.trans hPK) hDP hlU hl hcard hn
      hsmall (he.trans hp)).elim
  · exact ⟨g, he.trans hp⟩

/-- Application of the marked natural model to the literal checked quotient.
The B.2.14 supplement and its splitting are retained as explicit source
inputs; the conclusion is the ambient centralizer comparison used in 13.6.22. -/
theorem natural_marked_checked_centralizer
    (L K U : Subgroup G) (v : G) (a : Gv v) (F : Subgroup (Gcheck v))
    [IsMulCommutative F]
    (m : ConjugationQuotientModel K U W) (hK : K ≤ Gv v)
    (hpK : IsPPerfect 2 K) (hLK : Lv L v ≤ K)
    (hv : v ^ 2 = 1)
    (hmark : residual lineParabolicSL ≤ ((Lv L v).subgroupOf K).map m.actor)
    (ha : (a : G) ∈ centralizer (Lv L v : Set G))
    (haF : checkedQuotientMap v a ∈ F)
    (hsplit : F = checkedImage v U ⊔
      (F ⊓ centralizer (checkedImage v K : Set (Gcheck v)))) :
    K ≤ Gv (a : G) := by
  exact centralizes_of_ambient_centralizer_eq L K U v a F hK hpK hv hLK ha haF hsplit
    (natural_centralizer_eq m hLK hmark)

/-- The doubled branch uses one common actor and one common line mark on both
natural summands. -/
theorem doubled_marked_checked_centralizer
    (L K U : Subgroup G) (v : G) (a : Gv v) (F : Subgroup (Gcheck v))
    [IsMulCommutative F]
    (m : ConjugationQuotientModel K U (W.prod W)) (hK : K ≤ Gv v)
    (hpK : IsPPerfect 2 K) (hLK : Lv L v ≤ K)
    (hv : v ^ 2 = 1)
    (hmark : residual lineParabolicSL ≤ ((Lv L v).subgroupOf K).map m.actor)
    (ha : (a : G) ∈ centralizer (Lv L v : Set G))
    (haF : checkedQuotientMap v a ∈ F)
    (hsplit : F = checkedImage v U ⊔
      (F ⊓ centralizer (checkedImage v K : Set (Gcheck v)))) :
    K ≤ Gv (a : G) := by
  exact centralizes_of_ambient_centralizer_eq L K U v a F hK hpK hv hLK ha haF hsplit
    (doubled_centralizer_eq m hLK hmark)

/-! The following applications keep the source geometry visible: the marked
residual is obtained from the invariant four-group and the relative
two-group quotient, before invoking the checked centralizer comparison. -/

theorem exists_residual_marked_model (m : ConjugationQuotientModel K U ρ)
    (hPK : P ≤ K) (hDP : D ≤ P)
    (hlU : l ≤ U) (hl : ⁅l, D⁆ = l) (hcard : Nat.card l = 4)
    (hn : P ≤ normalizer (l : Set G))
    (S : Sylow 2 BinaryLinearThree.Group)
    (hS : (S : Subgroup BinaryLinearThree.Group) ≤ (P.subgroupOf K).map m.actor)
    (hproper : (P.subgroupOf K).map m.actor ≠ ⊤)
    (htwo : ¬ IsPGroup 2 ((P.subgroupOf K).map m.actor))
    (hsmall : ∀ H : Subgroup (Multiplicative V), Nat.card H ≤ 4 →
      (∀ g : pointParabolicSL, ∀ x : H,
        Multiplicative.ofAdd (ρ g (Multiplicative.toAdd (x : Multiplicative V))) ∈ H) →
      ∀ g : pointParabolicSL, ∀ x : H,
        ρ g (Multiplicative.toAdd (x : Multiplicative V)) =
          Multiplicative.toAdd (x : Multiplicative V))
    (hDN : (D.subgroupOf P).Normal)
    (hquot : letI := hDN; IsPGroup 2 (P ⧸ D.subgroupOf P)) :
    ∃ g : BinaryLinearThree.Group,
      (P.subgroupOf K).map (conjugate m g).actor = lineParabolicSL ∧
      residual lineParabolicSL ≤ (D.subgroupOf K).map (conjugate m g).actor := by
  obtain ⟨g, hg⟩ := exists_geometric_marking m hPK hDP hlU hl hcard hn
    S hS hproper htwo hsmall
  exact ⟨g, hg, hg ▸ image_residual_le (conjugate m g).actor hPK hDN hquot⟩

theorem natural_geometric_checked_centralizer
    (L K U P l : Subgroup G) (v : G) (a : Gv v) (F : Subgroup (Gcheck v))
    [IsMulCommutative F]
    (m : ConjugationQuotientModel K U W) (hK : K ≤ Gv v)
    (hpK : IsPPerfect 2 K) (hv : v ^ 2 = 1)
    (hPK : P ≤ K) (hDP : Lv L v ≤ P)
    (hlU : l ≤ U) (hl : ⁅l, Lv L v⁆ = l) (hcard : Nat.card l = 4)
    (hn : P ≤ normalizer (l : Set G))
    (S : Sylow 2 BinaryLinearThree.Group)
    (hS : (S : Subgroup BinaryLinearThree.Group) ≤ (P.subgroupOf K).map m.actor)
    (hproper : (P.subgroupOf K).map m.actor ≠ ⊤)
    (htwo : ¬ IsPGroup 2 ((P.subgroupOf K).map m.actor))
    (hDN : ((Lv L v).subgroupOf P).Normal)
    (hquot : letI := hDN; IsPGroup 2 (P ⧸ (Lv L v).subgroupOf P))
    (ha : (a : G) ∈ centralizer (Lv L v : Set G))
    (haF : checkedQuotientMap v a ∈ F)
    (hsplit : F = checkedImage v U ⊔
      (F ⊓ centralizer (checkedImage v K : Set (Gcheck v)))) :
    K ≤ Gv (a : G) := by
  obtain ⟨g, _, hg⟩ := exists_residual_marked_model m hPK hDP hlU hl hcard hn
    S hS hproper htwo point_invariant_small_fixed hDN hquot
  exact natural_marked_checked_centralizer L K U v a F (conjugate m g) hK hpK
    (hDP.trans hPK) hv hg ha haF hsplit

theorem doubled_geometric_checked_centralizer
    (L K U P l : Subgroup G) (v : G) (a : Gv v) (F : Subgroup (Gcheck v))
    [IsMulCommutative F]
    (m : ConjugationQuotientModel K U (W.prod W)) (hK : K ≤ Gv v)
    (hpK : IsPPerfect 2 K) (hv : v ^ 2 = 1)
    (hPK : P ≤ K) (hDP : Lv L v ≤ P)
    (hlU : l ≤ U) (hl : ⁅l, Lv L v⁆ = l) (hcard : Nat.card l = 4)
    (hn : P ≤ normalizer (l : Set G))
    (S : Sylow 2 BinaryLinearThree.Group)
    (hS : (S : Subgroup BinaryLinearThree.Group) ≤ (P.subgroupOf K).map m.actor)
    (hproper : (P.subgroupOf K).map m.actor ≠ ⊤)
    (htwo : ¬ IsPGroup 2 ((P.subgroupOf K).map m.actor))
    (hDN : ((Lv L v).subgroupOf P).Normal)
    (hquot : letI := hDN; IsPGroup 2 (P ⧸ (Lv L v).subgroupOf P))
    (ha : (a : G) ∈ centralizer (Lv L v : Set G))
    (haF : checkedQuotientMap v a ∈ F)
    (hsplit : F = checkedImage v U ⊔
      (F ⊓ centralizer (checkedImage v K : Set (Gcheck v)))) :
    K ≤ Gv (a : G) := by
  obtain ⟨g, _, hg⟩ := exists_residual_marked_model m hPK hDP hlU hl hcard hn
    S hS hproper htwo point_invariant_small_doubled_fixed hDN hquot
  exact doubled_marked_checked_centralizer L K U v a F (conjugate m g) hK hpK
    (hDP.trans hPK) hv hg ha haF hsplit

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch
