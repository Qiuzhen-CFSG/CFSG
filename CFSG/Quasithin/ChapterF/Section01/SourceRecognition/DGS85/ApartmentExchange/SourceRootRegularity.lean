module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.SourcePathRoots
public import Theory.GroupTheory.WeakBNPair.RegularTree.RootRegularity
public import Theory.GroupAction.RankTwoCosetGeometry.Kernels

/-!
# Regularity and order of the genuine source path roots

For the chosen reflection paths of length r = s-1, the odd s-path fixer
hypothesis makes every exit stabilizer in the actual path two-core trivial.
Together with the constructed root transitivity, this gives sharp
transitivity on all exits at both original marked endpoints. Evaluation
identifies the root with that exit set, so its order is the original
endpoint valence minus one. Its intersection with the full local
permutation kernel is trivial; the full kernel is not replaced by O₂.
Thickness also supplies a genuine root involution outside that kernel.

Finally the literal quotient map used by `pathFiniteQuotient` preserves
both root orders. Apartment uniqueness and exchange give separation, hence
injectivity on the original endpoints and their actual roots. This order
transport needs no BN root-sign premise. Reflection selection and the
regular-path and exchange inputs remain explicit. The final BN construction
still requires quotient root signs. In particular a root involution here does not
prove the prescribed conjugacy and centralization choice in (14.2), the
corrected (14.14), or the exceptional/regular alternative (14.19).

Source: DGS, *Groups and Graphs* (1985), Part II, (14.1), (14.2) and the
root notation, printed pp.210--211; (3.6)--(3.7), pp.77--80.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.GroupTheory.WeakBNPair.RegularTree Subgroup.CosetGeometry
open CFSG.Quasithin.ChapterF.Source
open CFSG.Quasithin.ChapterF.Source.SuzukiContainment
open CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension
open scoped Pointwise
namespace CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
namespace ReducedCartan
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable (h : HypothesisF11 L S) (c : CompatibleCartans L (reducedSylow L S))

variable (n : ℕ) (hn : 1 < n)
variable (t : Bool → (reducedAmalgam L S).Universal)
variable (htfix : ∀ i, t i • base (Universal.cosetFamily (reducedAmalgam L S)) i =
  base (Universal.cosetFamily (reducedAmalgam L S)) i)
variable (htmove : ∀ i, t i • base (Universal.cosetFamily (reducedAmalgam L S)) (!i) ≠
  base (Universal.cosetFamily (reducedAmalgam L S)) (!i))
variable (htsq : ∀ i, t i * t i = 1)
variable (htnorm : ∀ i, t i ∈
  Subgroup.normalizer (cartan c : Set (reducedAmalgam L S).Universal))
variable (htrans : BasedPathTransitive (X := (reducedAmalgam L S).Universal)
  (sourceGraph (reducedAmalgam L S)) (n+1))
variable (hthick : ∀ i, ∃ z, (sourceGraph (reducedAmalgam L S)).Adj
  (base (Universal.cosetFamily (reducedAmalgam L S)) i) z ∧
  z ≠ base (Universal.cosetFamily (reducedAmalgam L S)) (!i) ∧
  z ≠ t i • base (Universal.cosetFamily (reducedAmalgam L S)) (!i))

variable (hodd : ∀ {a b} (q : (sourceGraph (reducedAmalgam L S)).Walk a b),
  q.IsPath → q.length = n+1 →
    Odd (Nat.card (pathFixer (X := (reducedAmalgam L S).Universal) q)))

local notation "ρ" => pathRoots h c n hn t htfix htmove htsq htnorm htrans hthick

include hodd in
/-- The actual path radical has trivial stabilizer at every exit. -/
theorem pathRoots_exit_free (i : Bool) (z : SourceVertex (reducedAmalgam L S))
    (hz : (sourceGraph (reducedAmalgam L S)).Adj (ρ i).a z) (hzprev : z ≠ (ρ i).b) :
    (ρ i).root ⊓ MulAction.stabilizer (reducedAmalgam L S).Universal z = ⊥ := by
  let p := reflectionPath c t htfix htmove htnorm n (by omega) i
  have htree := (Universal.cosetGraph_isTree (reducedAmalgam L S)
    (inclusion_injective (commonBorel_le_parabolic 0))
    (inclusion_injective (commonBorel_le_parabolic 1))).isAcyclic
  change (sourceGraph (reducedAmalgam L S)).Adj
    (base (Universal.cosetFamily (reducedAmalgam L S)) i) z at hz
  have hpz : z ≠ p.walk.penultimate := hzprev
  have hnew : z ∉ p.walk.support := fun hm =>
    hpz (htree.eq_penultimate_of_adj_end p.isPath hz hm)
  exact pathRoot_inf_stabilizer_eq_bot p.walk hz
    (hodd (p.walk.concat hz) (p.isPath.concat hnew hz)
      (by rw [SimpleGraph.Walk.length_concat, p.length_eq]))

include hodd in
/-- Evaluation at the chosen reflected exit is injective on the literal path root. -/
theorem pathRoots_exit_injective (i : Bool) :
    Function.Injective (fun x : (ρ i).root => (x : (reducedAmalgam L S).Universal) • (ρ i).c) := by
  intro x y hxy
  apply Subtype.ext
  apply inv_mul_eq_one.mp
  have hm : (x : (reducedAmalgam L S).Universal)⁻¹ * y ∈
      (ρ i).root ⊓ MulAction.stabilizer (reducedAmalgam L S).Universal (ρ i).c := by
    refine ⟨(ρ i).root.mul_mem ((ρ i).root.inv_mem x.property) y.property, ?_⟩
    change ((x : (reducedAmalgam L S).Universal)⁻¹ * y) • (ρ i).c = (ρ i).c
    change (x : (reducedAmalgam L S).Universal) • (ρ i).c =
      (y : (reducedAmalgam L S).Universal) • (ρ i).c at hxy
    rw [mul_smul, ← hxy, inv_smul_smul]
  rw [pathRoots_exit_free h c n hn t htfix htmove htsq htnorm htrans hthick hodd
    i (ρ i).c (ρ i).adj_c (ρ i).distinct.symm] at hm
  exact hm

include hodd in
/-- The actual roots act sharply transitively on the exits at both marked endpoints. -/
theorem pathRoots_sharply_transitive (i : Bool) (z : SourceVertex (reducedAmalgam L S))
    (hz : (sourceGraph (reducedAmalgam L S)).Adj (ρ i).a z) (hzprev : z ≠ (ρ i).b) :
    ∃! x : (ρ i).root, (x : (reducedAmalgam L S).Universal) • (ρ i).c = z := by
  obtain ⟨x, hx, he⟩ := (ρ i).transitive z hz hzprev
  exact ⟨⟨x, hx⟩, he, fun y hy => pathRoots_exit_injective h c n hn t htfix htmove
    htsq htnorm htrans hthick hodd i (hy.trans he.symm)⟩

/-- Evaluation identifies each actual root with its endpoint exits. -/
def pathRootsExitEquiv (i : Bool) : (ρ i).root ≃
    pathExit (reflectionPath c t htfix htmove htnorm n (by omega) i).walk :=
  Equiv.ofBijective
    (fun x => ⟨(x : (reducedAmalgam L S).Universal) • (ρ i).c,
      pathRoot_smul_exit (source_action (reducedAmalgam L S))
        (reflectionPath c t htfix htmove htnorm n (by omega) i).walk
        ⟨(ρ i).c, (ρ i).adj_c, (ρ i).distinct.symm⟩ x⟩)
    ⟨fun x y he => pathRoots_exit_injective h c n hn t htfix htmove htsq htnorm htrans
      hthick hodd i (congrArg Subtype.val he), by
      intro z
      obtain ⟨x, hx, he⟩ := (ρ i).transitive z z.property.1 z.property.2
      exact ⟨⟨x, hx⟩, Subtype.ext he⟩⟩

include hodd in
/-- The root order is exactly the original marked endpoint valence minus one. -/
theorem pathRoots_card_add_one (i : Bool) :
    Nat.card (ρ i).root + 1 = Nat.card ((sourceGraph (reducedAmalgam L S)).neighborSet
      (base (Universal.cosetFamily (reducedAmalgam L S)) i)) := by
  let := (reduced_hypothesis h).finite_parabolic 0
  let := (reduced_hypothesis h).finite_parabolic 1
  let p := reflectionPath c t htfix htmove htnorm n (by omega) i
  have := (source_finite_valence (reducedAmalgam L S)
    (base (Universal.cosetFamily (reducedAmalgam L S)) i)).fintype
  rw [Nat.card_congr (pathRootsExitEquiv h c n hn t htfix htmove htsq htnorm htrans hthick hodd i)]
  apply card_pathExit p.walk
  intro he
  have hz := he.length_eq_zero
  rw [p.length_eq] at hz
  omega

include hodd in
/-- Both root orders equal the intrinsic endpoint/overlap index minus one. -/
theorem pathRoots_card_eq_index (i : Bool) : Nat.card (ρ i).root + 1 =
    ((Universal.cosetFamily (reducedAmalgam L S) (!i)).subgroupOf
      (Universal.cosetFamily (reducedAmalgam L S) i)).index := by
  rw [pathRoots_card_add_one h c n hn t htfix htmove htsq htnorm htrans hthick hodd]
  exact RankTwo.card_neighbor_base _ i

include hodd in
/-- The root meets the full local permutation kernel trivially; this does not identify that kernel with O₂. -/
theorem pathRoots_inf_localKernel (i : Bool) : (ρ i).root ⊓
    RankTwo.ballKernel (Universal.cosetFamily (reducedAmalgam L S))
      (base (Universal.cosetFamily (reducedAmalgam L S)) i) 1 = ⊥ := by
  apply le_bot_iff.mp
  intro x hx
  have hf : x ∈ MulAction.stabilizer (reducedAmalgam L S).Universal (ρ i).c :=
    hx.2 (ρ i).c ((RankTwo.mem_ball_one _ _ _).mpr (Or.inl (ρ i).adj_c))
  have hm : x ∈ (ρ i).root ⊓ MulAction.stabilizer (reducedAmalgam L S).Universal (ρ i).c :=
    ⟨hx.1, hf⟩
  rw [pathRoots_exit_free h c n hn t htfix htmove htsq htnorm htrans hthick hodd
    i (ρ i).c (ρ i).adj_c (ρ i).distinct.symm] at hm
  exact hm

/-- Thickness supplies an involution in the genuine root; no finiteness of the universal completion is used. -/
theorem pathRoots_exists_involution (i : Bool) :
    ∃ x ∈ (ρ i).root, orderOf x = 2 := by
  obtain ⟨z, hz, hzb, hzc⟩ := (ρ i).thick
  obtain ⟨x, hx, he⟩ := (ρ i).transitive z hz hzb
  let v : (ρ i).root := ⟨x, hx⟩
  have hv : v ≠ 1 := by
    intro hh
    have hxone : x = 1 := congrArg Subtype.val hh
    rw [hxone, one_smul] at he
    exact hzc he.symm
  have htwo : IsPGroup 2 (ρ i).root := pathRoot_isTwo _
  obtain ⟨k, hk⟩ := htwo.exists_orderOf_eq_pow v
  let w : (ρ i).root := v ^ (orderOf v / 2)
  have hw : orderOf w = 2 := orderOf_pow_orderOf_div
    (by rw [hk]; exact pow_ne_zero _ (by decide)) (htwo.dvd_orderOf hv)
  exact ⟨w, w.property, (Subgroup.orderOf_coe w).trans hw⟩

include hodd in
/-- The root involution survives the full local permutation action, as required before the source conjugacy choice. -/
theorem pathRoots_exists_involution_outside_localKernel (i : Bool) :
    ∃ x ∈ (ρ i).root, orderOf x = 2 ∧
      x ∉ RankTwo.ballKernel (Universal.cosetFamily (reducedAmalgam L S))
        (base (Universal.cosetFamily (reducedAmalgam L S)) i) 1 := by
  obtain ⟨x, hx, ho⟩ := pathRoots_exists_involution h c n hn t htfix htmove htsq htnorm
    htrans hthick i
  refine ⟨x, hx, ho, ?_⟩
  intro hk
  have hm : x ∈ (ρ i).root ⊓
      RankTwo.ballKernel (Universal.cosetFamily (reducedAmalgam L S))
        (base (Universal.cosetFamily (reducedAmalgam L S)) i) 1 := ⟨hx, hk⟩
  rw [pathRoots_inf_localKernel h c n hn t htfix htmove htsq htnorm htrans hthick hodd i] at hm
  have he : orderOf x = 1 := orderOf_eq_one_iff.mpr hm
  omega

variable (hexchange : ChosenApartmentExchange (X := (reducedAmalgam L S).Universal)
  (sourceGraph (reducedAmalgam L S))
    (cartanApartment (reducedAmalgam L S) (apartmentGroup c (pathRoots h c n hn t htfix htmove htsq htnorm htrans hthick))) n)

include hodd hexchange in
/-- Exchange and odd path fixers make the literal quotient injective on each actual root. -/
theorem pathRoots_quotient_injOn (i : Bool) :
    Set.InjOn (quotientMap (reducedAmalgam L S)
      (cartanApartment (reducedAmalgam L S) (apartmentGroup c ρ)) n) (ρ i).root := by
  let := (reduced_hypothesis h).finite_parabolic 0
  let := (reduced_hypothesis h).finite_parabolic 1
  let A := reducedAmalgam L S
  let N := apartmentGroup c ρ
  have ha := pathRoots_a h c n hn t htfix htmove htsq htnorm htrans hthick
  have hb := pathRoots_b h c n hn t htfix htmove htsq htnorm htrans hthick
  have hnormalizes := pathRoots_normalizes h c n hn t htfix htmove htsq htnorm htrans hthick
  have hinv := pathRoots_square h c n hn t htfix htmove htsq htnorm htrans hthick
  have hnorm := apartmentGroup_normalizes c ρ hnormalizes
  have hlift := reflection_mem_apartmentGroup c ρ
  have hL := inclusion_injective (commonBorel_le_parabolic (L := L)
    (S := reducedSylow L S) 0)
  have hR := inclusion_injective (commonBorel_le_parabolic (L := L)
    (S := reducedSylow L S) 1)
  have hline := cartanApartment_noBranching A N (cartan c) ρ ha hb hlift
    (cartan_le c) hnorm le_rfl hinv hL hR
  have hunique : ApartmentsUnique (X := A.Universal) (sourceGraph A)
      (cartanApartment A N) (n+1) := cartanApartment_unique A N ρ ha hb hlift hline (cartan c)
    (cartan_le_apartmentGroup c ρ) (cartan_le c) hnorm hL hR n (cartan_hall c) hodd
  have hsep : Separated (sourceRelation A (cartanApartment A N) n) (sourceGraph A) (2*n) :=
    source_apartment_separated A (cartanApartment A N) n hL hR htrans
    hline hunique hexchange (by omega)
  have hroot : (ρ i).root ≤ Universal.cosetFamily A i := by
    have hfix := (ρ i).root_fixes.trans inf_le_left
    simpa only [pathRoots_a, stabilizer_base] using hfix
  exact (quotient_injOn_endpoint A (cartanApartment A N) n hL hR hsep hn
    (original_core_eq_bot h) i).mono hroot

include hodd hexchange in
/-- The image root retains its order in the actual universal-completion quotient, before any BN root-sign assumption. -/
theorem pathRoots_card_quotientImage (i : Bool) :
    Nat.card ((ρ i).root.map (quotientMap (reducedAmalgam L S)
      (cartanApartment (reducedAmalgam L S) (apartmentGroup c ρ)) n)) =
      Nat.card (ρ i).root :=
  Nat.card_image_of_injOn
    (pathRoots_quotient_injOn h c n hn t htfix htmove htsq htnorm htrans
      hthick hodd hexchange i)

include hodd hexchange in
/-- Both quotient root orders equal the original endpoint valence minus one. -/
theorem pathRoots_card_quotientImage_add_one (i : Bool) :
    Nat.card ((ρ i).root.map (quotientMap (reducedAmalgam L S)
      (cartanApartment (reducedAmalgam L S) (apartmentGroup c ρ)) n)) + 1 =
      Nat.card ((sourceGraph (reducedAmalgam L S)).neighborSet
        (base (Universal.cosetFamily (reducedAmalgam L S)) i)) :=
  (congrArg (· + 1) (pathRoots_card_quotientImage h c n hn t htfix htmove htsq htnorm htrans
    hthick hodd hexchange i)).trans
      (pathRoots_card_add_one h c n hn t htfix htmove htsq htnorm htrans hthick hodd i)

end ReducedCartan
end CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
