module
public import Theory.GroupTheory.PGroup.CharacteristicCenterReduction
public import Theory.GroupTheory.PGroup.NormalSubgroups
public import Stellmacher.OmegaOneCenterMap

/-!
# Irreducible sections detected by a Sylow-center seed

Let S be normal in a finite two-group P, and let E/Z₀ be an irreducible
section for another subgroup B. Suppose the center of S/Z₀ lies in E/Z₀.
For normal ambient subgroups Z and F with Z₀ ≤ Z ≤ S and Z ≤ F, assume
that the omega-center of the image of P in G/Z lies in the image of F.
Then E lies in F.

Irreducibility first gives E ∩ Z = Z₀ or E ≤ Z. In the first case the
normal-center intersection theorem applied in S/Z₀ forces Z = Z₀. A
central involution in the nontrivial normal image of S inside P/Z then
lies in E ∩ F outside Z₀. Irreducibility gives E ≤ F. The second case
follows directly from Z ≤ F.

Source application: Aschbacher--Smith, 14.6.9(k), printed p.1027.
Only the containment in the normal subgroup F is required by the endgame.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

private theorem normal_eq_of_quotient_center_bound {p : ℕ} [Fact p.Prime]
    (hp : IsPGroup p G) (Z N E : Subgroup G) [Z.Normal] [N.Normal]
    (hZN : Z ≤ N) (hcenter : (center (G ⧸ Z)).comap (QuotientGroup.mk' Z) ≤ E)
    (hinf : N ⊓ E = Z) : N = Z := by
  let q := QuotientGroup.mk' Z
  have hi : N.map q = ⊥ := by
    by_contra hne
    have hh := center_inf_ne_bot_of_normal (hp.to_quotient Z) (N.map q) hne
    obtain ⟨x,hx,hxne⟩ :=
      (center (G ⧸ Z) ⊓ N.map q).bot_or_exists_ne_one.resolve_left hh
    obtain ⟨n,hn,he⟩ := hx.2
    have hnE : n ∈ E := hcenter (show q n ∈ center (G ⧸ Z) from he.symm ▸ hx.1)
    have hnZ : n ∈ Z := hinf ▸ (show n ∈ N ⊓ E from ⟨hn,hnE⟩)
    exact hxne (he.symm.trans ((QuotientGroup.eq_one_iff n).mpr hnZ))
  apply le_antisymm _ hZN
  simpa only [q, QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff N).mp hi

private theorem exists_omega_center_in_normal_two (hp : IsPGroup 2 G)
    (N : Subgroup G) [N.Normal] (hne : N ≠ ⊥) :
    ∃ x : G, x ∈ N ∧ x ≠ 1 ∧ x^2=1 ∧ x ∈ center G := by
  let : Fact (IsPGroup 2 G) := ⟨hp⟩
  let : Nontrivial N := (nontrivial_iff_ne_bot N).mpr hne
  obtain ⟨A,_,hAN,hAc,hAZ⟩ :=
    exists_central_subgroup_card_eq_prime_in_normal (p := 2) N inferInstance
  have hA : A ≠ ⊥ := by intro he; simp [he] at hAc
  obtain ⟨x,hx,hxne⟩ := A.bot_or_exists_ne_one.resolve_left hA
  refine ⟨x,hAN hx,hxne,?_,hAZ hx⟩
  have hh := pow_card_eq_one' (x := (⟨x,hx⟩ : A))
  rw [hAc] at hh
  exact congrArg Subtype.val hh
end Theory.GroupTheory

namespace Theory.GroupTheory
open Stellmacher
variable {G : Type*} [Group G] [Finite G]

/-- A central involution of the normal quotient detects the entire
irreducible section inside the ambient normal subgroup. -/
theorem irreducible_section_le_normal_of_omega_quotient
    (P S B E Z₀ Z F : Subgroup G) (hP : IsPGroup 2 P)
    (hSP : S ≤ P) (hSnormal : (S.subgroupOf P).Normal)
    (hES : E ≤ S) (hZS : Z ≤ S) (hZ₀Z : Z₀ ≤ Z)
    [Z.Normal] [F.Normal] [(Z₀.subgroupOf S).Normal]
    (hE : B ≤ normalizer (E : Set G))
    (hirr : IsIrreducibleSection B Z₀ E)
    (hcenter : ((center (S ⧸ Z₀.subgroupOf S)).comap
      (QuotientGroup.mk' (Z₀.subgroupOf S))).map S.subtype ≤ E)
    (hZF : Z ≤ F)
    (hseed : omegaOneCenterAmbient (P.map (QuotientGroup.mk' Z)) ≤
      F.map (QuotientGroup.mk' Z)) : E ≤ F := by
  have hZ₀E := hirr.1
  have hZ₀S := hZ₀E.trans hES
  have hinv (A : Subgroup G) [A.Normal] : IsConjugateInvariantBy (E ⊓ A) B := by
    intro b a ha
    exact ⟨(mem_normalizer_iff.mp (hE b.property) a).mp ha.1,
      (inferInstance : A.Normal).conj_mem a ha.2 b⟩
  rcases hirr.2.2 (E ⊓ Z) (le_inf hZ₀E hZ₀Z) inf_le_left (hinv Z) with hz | he
  · have hZZ₀ : Z = Z₀ := by
      have heq : Z.subgroupOf S = Z₀.subgroupOf S :=
        normal_eq_of_quotient_center_bound (hP.to_le hSP)
          (Z₀.subgroupOf S) (Z.subgroupOf S) (E.subgroupOf S)
          (comap_mono hZ₀Z) (by
            intro x hx
            exact hcenter (mem_map_of_mem S.subtype hx)) (by
            change Z.comap S.subtype ⊓ E.comap S.subtype = Z₀.comap S.subtype
            rw [←comap_inf,inf_comm Z E,hz])
      have hh := congrArg (Subgroup.map S.subtype) heq
      simpa only [map_subgroupOf_eq_of_le hZS,map_subgroupOf_eq_of_le hZ₀S] using hh
    let q := QuotientGroup.mk' Z
    let Pq := P.map q
    let Sq := S.map q
    have hSqPq : Sq ≤ Pq := map_mono hSP
    have hPS : P ≤ normalizer (S : Set G) :=
      (normal_subgroupOf_iff_le_normalizer hSP).mp hSnormal
    have hPqSq : Pq ≤ normalizer (Sq : Set (G ⧸ Z)) :=
      (map_mono hPS).trans (S.le_normalizer_map q)
    let : (Sq.subgroupOf Pq).Normal :=
      (normal_subgroupOf_iff_le_normalizer hSqPq).mpr hPqSq
    have hSqne : Sq ≠ ⊥ := by
      intro hbot
      have hSZ : S ≤ Z := by
        simpa only [q,QuotientGroup.ker_mk'] using (map_eq_bot_iff S).mp hbot
      exact hirr.2.1 (le_antisymm hZ₀E (hES.trans (hSZ.trans_eq hZZ₀)))
    have hSqrne : Sq.subgroupOf Pq ≠ ⊥ := by
      intro hh
      have heq := congrArg (Subgroup.map Pq.subtype) hh
      rw [map_subgroupOf_eq_of_le hSqPq,Subgroup.map_bot] at heq
      exact hSqne heq
    obtain ⟨x,hx,hxne,hx2,hxz⟩ := exists_omega_center_in_normal_two
      (hP.map q) (Sq.subgroupOf Pq) hSqrne
    obtain ⟨s,hs,hqs⟩ := hx
    have hsF : s ∈ F := by
      have hxomega : (x : G ⧸ Z) ∈ omegaOneCenterAmbient Pq :=
        (mem_omegaOneCenterAmbient_iff _ _).mpr
          ⟨x.property,congrArg Subtype.val hx2,fun y hy =>
            congrArg Subtype.val ((mem_center_iff.mp hxz) ⟨y,hy⟩)⟩
      have hh : q s ∈ F.map q := hqs.symm ▸ hseed hxomega
      have hi := (show s ∈ (F.map q).comap q from hh)
      rw [comap_map_eq,QuotientGroup.ker_mk',sup_eq_left.mpr hZF] at hi
      exact hi
    have hsE : s ∈ E := by
      have hscenter : (QuotientGroup.mk' (Z₀.subgroupOf S)) ⟨s,hs⟩ ∈
          center (S ⧸ Z₀.subgroupOf S) := by
        apply mem_center_iff.mpr
        intro y
        obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (Z₀.subgroupOf S) y
        change (QuotientGroup.mk' (Z₀.subgroupOf S)) (a * ⟨s,hs⟩) =
          (QuotientGroup.mk' (Z₀.subgroupOf S)) (⟨s,hs⟩ * a)
        apply QuotientGroup.eq_iff_div_mem.mpr
        change ((a : G) * s) / (s * (a : G)) ∈ Z₀
        rw [←hZZ₀]
        apply QuotientGroup.eq_iff_div_mem.mp
        change q ((a : G) * s) = q (s * (a : G))
        rw [map_mul,map_mul,hqs]
        exact congrArg Subtype.val ((mem_center_iff.mp hxz)
          ⟨q a,mem_map_of_mem q (hSP a.property)⟩)
      exact hcenter ⟨⟨s,hs⟩,hscenter,rfl⟩
    rcases hirr.2.2 (E ⊓ F) (le_inf hZ₀E (hZ₀Z.trans hZF)) inf_le_left (hinv F) with hf | hf
    · have hsZ : s ∈ Z := hZZ₀.symm ▸ (hf ▸ (show s ∈ E ⊓ F from ⟨hsE,hsF⟩))
      exact (hxne (Subtype.ext (hqs.symm.trans ((QuotientGroup.eq_one_iff s).mpr hsZ)))).elim
    · rw [←hf]
      exact inf_le_right
  · rw [←he]
    exact inf_le_right.trans hZF
end Theory.GroupTheory
