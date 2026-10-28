module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.EightGenerating
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.EightGenerating
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.FullSeed
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowCompatible

/-!
# Compatible common fixed subgroup for the image-eight small movers

The canonical paired selection in `SectionFive.EightGenerating` uses the
same order-three permutation and the same two possible mover generators.
Their four original/conjugate generators have no nonzero common fixed
vector in the deleted six-letter module. The full seed admits ordinary
six-letter displacement coordinates after the given small critical pair;
the core coordinate map has only constant vectors in its kernel. Thus a
seed vector fixed by both chosen movers is fixed by the whole stabilizer.

The finite fixed-space certificate is transported through the producer's
canonical conjugator and its literal quotient lifts while retaining every
original generation equation. The graph consumer preserves both moved
covers, all central attachments, and the same g, x, edge t and mover J.
The private imports intentionally reuse the producer's precise canonical
model and full-seed coordinate formulas; no claim is made for arbitrary
existential witnesses from the earlier selection theorem.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (5.6)(b), printed p.917; used by the kernel-normalization argument
in (5.12)(1), printed pp.924--925.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open Theory.SpecificGroups.SymmetricSix
open scoped commutatorElement Pointwise IsMulCommutative
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.EightCompatible
local notation "S" => Equiv.Perm (Fin 6)
open CubeCommonFixer hiding r t k
open SectionFive.EightGenerating

private theorem four_generators_deleted_fixed (m : Fin 2) (H : Subgroup S)
    (hz : z ∈ H) (hy : y m ∈ H)
    (hzr : (MulAut.conj r⁻¹) z ∈ H)
    (hyr : (MulAut.conj r⁻¹) (y m) ∈ H) :
    fixedSpace (deletedRepresentation (Fin 6)) H = ⊥ := by
  apply bot_unique
  intro v hv
  obtain ⟨w,rfl⟩ := (constants (Fin 6)).mkQ_surjective v
  have hz' : representation (Fin 6) z w = w :=
    (deleted_fixed_iff_of_fixed_point z w 4 (by decide +kernel)).mp (hv ⟨z,hz⟩)
  have hy' : representation (Fin 6) (y m) w = w :=
    (deleted_fixed_iff_of_fixed_point (y m) w 2 (by fin_cases m <;> decide +kernel)).mp (hv ⟨y m,hy⟩)
  have hzr' : representation (Fin 6) ((MulAut.conj r⁻¹) z) w = w :=
    (deleted_fixed_iff_of_fixed_point _ w 3 (by decide +kernel)).mp (hv ⟨_,hzr⟩)
  have hyr' : representation (Fin 6) ((MulAut.conj r⁻¹) (y m)) w = w :=
    (deleted_fixed_iff_of_fixed_point _ w 0 (by fin_cases m <;> decide +kernel)).mp (hv ⟨_,hyr⟩)
  have cert : ∀ (m : Fin 2) (w : Full (Fin 6)),
      representation (Fin 6) z w = w → representation (Fin 6) (y m) w = w →
      representation (Fin 6) ((MulAut.conj r⁻¹) z) w = w →
      representation (Fin 6) ((MulAut.conj r⁻¹) (y m)) w = w →
      ∀ i, w i = w 0 := by decide +kernel
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    ((mem_constants_iff w).mpr ⟨w 0,cert m w hz' hy' hzr' hyr'⟩)

private theorem core_kernel_constant {Y : Type*} [AddCommGroup Y] [Module (ZMod 2) Y]
    (ρ : Representation (ZMod 2) S Y)
    (j : (coreRepresentation (Fin 6)).IntertwiningMap ρ)
    (hj : ∀ i k : Fin 6, i ≠ k → j (SeedCoordinates.pairVector i k) ≠ 0)
    (v : core (Fin 6)) (hv : j v = 0) : v.val ∈ constants (Fin 6) := by
  apply (mem_constants_iff v.val).mpr
  refine ⟨v.val 0,?_⟩
  intro i
  by_cases hi : i = 0
  · rw [hi]
  have he : coreRepresentation (Fin 6) (Equiv.swap i 0) v-v =
      (v.val i+v.val 0) • SeedCoordinates.pairVector i 0 :=
    SeedCoordinates.displacement_swap v.val i 0
  have hz : (v.val i+v.val 0) • j (SeedCoordinates.pairVector i 0) = 0 := by
    rw [←map_smul,←he,map_sub,j.isIntertwining,hv,map_zero,sub_self]
  have hc : v.val i+v.val 0 = 0 := (smul_eq_zero.mp hz).resolve_right (hj i 0 hi)
  exact (by decide : ∀ a b : ZMod 2, a+b=0 → a=b) _ _ hc

private theorem seed_fixed_of_deleted_fixed
    {Y : Type*} [AddCommGroup Y] [Module (ZMod 2) Y]
    (ρ : Representation (ZMod 2) S Y)
    (j : (coreRepresentation (Fin 6)).IntertwiningMap ρ)
    (hj : ∀ i k : Fin 6, i ≠ k → j (SeedCoordinates.pairVector i k) ≠ 0)
    (H : Subgroup S) (hH : fixedSpace (deletedRepresentation (Fin 6)) H = ⊥)
    (v : Y) (w : Full (Fin 6))
    (hw : ∀ g : S, ρ g v-v = j (SeedCoordinates.displacement g w))
    (hv : ∀ g ∈ H, ρ g v=v) : ∀ g : S, ρ g v=v := by
  have hfix : (constants (Fin 6)).mkQ w ∈ fixedSpace (deletedRepresentation (Fin 6)) H := by
    intro g
    apply (deleted_fixed_iff g.val w).mpr
    apply (mem_constants_iff _).mp
    exact core_kernel_constant ρ j hj (SeedCoordinates.displacement g.val w)
      ((hw g.val).symm.trans (sub_eq_zero.mpr (hv g.val g.property)))
  rw [hH] at hfix
  have hconst : w ∈ constants (Fin 6) := (Submodule.Quotient.mk_eq_zero _).mp hfix
  obtain ⟨c,hc⟩ := (mem_constants_iff w).mp hconst
  intro g
  apply sub_eq_zero.mp
  rw [hw]
  have he : SeedCoordinates.displacement g w = 0 := by
    apply Subtype.ext
    ext i
    change w (g.symm i)-w i=0
    rw [hc,hc,sub_self]
  rw [he,map_zero]

private theorem canonical_deleted_fixed (E : Subgroup S) (hES : E ≤ sylowCarrier)
    (hne : ¬ IsElementaryAbelian 2 E)
    (hy : ∃ w ∈ E ⊓ D 6, w (4 : Fin 6) ≠ 4) :
    let J := E ⊓ D 6
    fixedSpace (deletedRepresentation (Fin 6))
      (J ⊔ J.map (MulAut.conj r⁻¹).toMonoidHom) = ⊥ := by
  let J := E ⊓ D 6
  have hex : ∃ x ∈ E, x^2 ≠ 1 := by
    by_contra! hh
    exact hne (NonsylowImage.elementary_of_squares E hh)
  obtain ⟨x,hx,hsq⟩ := hex
  obtain ⟨i,rfl⟩ := (mem_sylowCarrier_iff _).mp (hES hx)
  have hz : z ∈ J := by
    have he := (NonsylowImage.sylow_square_certificate i).resolve_left hsq
    change (sylowWords i)^2=z at he
    exact ⟨he ▸ E.pow_mem hx 2,(mem_disjointTranspositions_iff (3 : Fin 4) _).mpr ⟨3,by decide +kernel⟩⟩
  obtain ⟨w,hw,hw4⟩ := hy
  obtain ⟨j,rfl⟩ := (mem_disjointTranspositions_iff (3 : Fin 4) _).mp hw.2
  obtain ⟨m,hm⟩ : ∃ m : Fin 2, y m ∈ J := by
    have cert : ∀ j : Fin 8, dWords j (4 : Fin 6) ≠ 4 →
        ∃ m : Fin 2, y m = dWords j ∨ y m = z*dWords j := by decide +kernel
    obtain ⟨m,he | he⟩ := cert j hw4
    · exact ⟨m,he ▸ hw⟩
    · exact ⟨m,he ▸ J.mul_mem hz hw⟩
  exact four_generators_deleted_fixed m _ (mem_sup_left hz) (mem_sup_left hm)
    (mem_sup_right (mem_map_of_mem _ hz)) (mem_sup_right (mem_map_of_mem _ hm))

private theorem deleted_fixed_bot_conjugate (H : Subgroup S)
    (hH : fixedSpace (deletedRepresentation (Fin 6)) H = ⊥) (g : S) :
    fixedSpace (deletedRepresentation (Fin 6)) (H.map (MulAut.conj g).toMonoidHom) = ⊥ := by
  apply Submodule.finrank_eq_zero.mp
  rw [←(fixedSpaceConjEquiv (deletedRepresentation (Fin 6)) H g).finrank_eq,hH]
  simp

private theorem compatible_pair_fixed (E J : Subgroup S) (u : S)
    (hES : E ≤ sylowCarrier.map (MulAut.conj u).toMonoidHom)
    (hEcard : Nat.card E = 8) (hne : ¬ IsElementaryAbelian 2 E)
    (hJ : J = E ⊓ (D 6).map (MulAut.conj u).toMonoidHom)
    (hmodel : IsConjugateTo J plus ∨ IsConjugateTo J (evenPart 6))
    (v : S) (hv : v.IsSwap) :
    ∃ w x : S, x ∈ alternatingGroup (Fin 6) ∧ orderOf x = 3 ∧
      let J₁ := J.map (MulAut.conj w).toMonoidHom
      let E₁ := E.map (MulAut.conj w).toMonoidHom
      J₁ ⊔ zpowers v ⊔ zpowers ((MulAut.conj x) v) = ⊤ ∧
      x⁻¹ ∈ J₁ ⊔ J₁.map (MulAut.conj x⁻¹).toMonoidHom ∧
      E₁ ⊔ zpowers v = ⊤ ∧ E₁ ⊔ zpowers ((MulAut.conj x) v) = ⊤ ∧
      fixedSpace (deletedRepresentation (Fin 6))
        (J₁ ⊔ J₁.map (MulAut.conj x⁻¹).toMonoidHom) = ⊥ := by
  let f := (MulAut.conj u⁻¹).toMonoidHom
  have back (A : Subgroup S) : (A.map (MulAut.conj u).toMonoidHom).map f = A := by
    rw [conjugate_twice,inv_mul_cancel,
      show (MulAut.conj (1 : S)).toMonoidHom = MonoidHom.id S from rfl,map_id]
  have hE : E.map f ≤ sylowCarrier := (map_mono hES).trans_eq (back _)
  have hn : ¬ IsElementaryAbelian 2 (E.map f) := by
    intro hh
    let := hh
    apply hne
    apply NonsylowImage.elementary_of_squares
    intro x hx
    apply (MulAut.conj u⁻¹).injective
    rw [map_pow,map_one]
    exact elemPow_eq_one_of_isElementaryAbelian _ (mem_map_of_mem f hx)
  have hJF : J.map f = E.map f ⊓ D 6 := by
    rw [hJ,map_inf _ _ _ (MulAut.conj u⁻¹).injective,back]
  obtain ⟨m,r₀,hr⟩ : ∃ m : Fin 2, ∃ r₀ : S,
      J = (EightSelection.model m).map (MulAut.conj r₀).toMonoidHom := by
    rcases hmodel with ⟨r,hr⟩ | ⟨r,hr⟩
    · exact ⟨0,r,hr⟩
    · exact ⟨1,r,hr⟩
  have hmove : ∃ y ∈ E.map f ⊓ D 6, y (4 : Fin 6) ≠ 4 := by
    rw [←hJF,hr,conjugate_twice]
    exact EightStrictShift.model_moves m (u⁻¹*r₀) 4
  have hcard : Nat.card (E.map f) = 8 := by
    rw [card_map_of_injective (MulAut.conj u⁻¹).injective,hEcard]
  obtain ⟨hgen,hpair,hleft,hright⟩ := canonical_pair (E.map f) hE hcard hn hmove
  have hfixed := canonical_deleted_fixed (E.map f) hE hn hmove
  rw [←hJF] at hgen hpair hfixed
  obtain ⟨v₀,hv₀⟩ := swap_conjugator v hv
  let k₀ : S := v₀.val * Equiv.swap 1 4
  have hk : (MulAut.conj k₀).toMonoidHom t = v := by
    have cert : (MulAut.conj (Equiv.swap (1 : Fin 6) 4)) t = a := by decide +kernel
    change (MulAut.conj v₀.val) ((MulAut.conj (Equiv.swap 1 4)) t) = v
    rw [cert]
    exact hv₀
  let x := (MulAut.conj k₀) r
  have hx : x ∈ alternatingGroup (Fin 6) :=
    (inferInstance : (alternatingGroup (Fin 6)).Normal).conj_mem r (by decide +kernel) k₀
  have ht : (MulAut.conj k₀).toMonoidHom ((MulAut.conj r) t) = (MulAut.conj x) v := by
    rw [←hk]
    change k₀*(r*t*r⁻¹)*k₀⁻¹ = (k₀*r*k₀⁻¹)*(k₀*t*k₀⁻¹)*(k₀*r*k₀⁻¹)⁻¹
    group
  have hJx : ((J.map f).map (MulAut.conj r⁻¹).toMonoidHom).map (MulAut.conj k₀).toMonoidHom =
      ((J.map f).map (MulAut.conj k₀).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom := by
    rw [conjugate_twice (J.map f),conjugate_twice (J.map f)]
    have he : k₀*r⁻¹=x⁻¹*k₀ := by change k₀*r⁻¹=(k₀*r*k₀⁻¹)⁻¹*k₀; group
    rw [he]
  refine ⟨k₀*u⁻¹,x,hx,((MulAut.conj k₀).orderOf_eq r).trans
    (orderOf_eq_prime (by decide +kernel) (by decide +kernel)),?_,?_,?_,?_,?_⟩
  · have hh := congrArg (Subgroup.map (MulAut.conj k₀).toMonoidHom) hgen
    simpa only [Subgroup.map_sup,MonoidHom.map_zpowers,hk,ht,f,conjugate_twice,
      map_top_of_surjective (MulAut.conj k₀).toMonoidHom (MulAut.conj k₀).surjective] using hh
  · have hh := mem_map_of_mem (MulAut.conj k₀).toMonoidHom hpair
    rw [Subgroup.map_sup,hJx] at hh
    have hri : (MulAut.conj k₀).toMonoidHom r⁻¹ = x⁻¹ := (MulAut.conj k₀).map_inv r
    simpa only [hri,f,conjugate_twice] using hh
  · have hh := congrArg (Subgroup.map (MulAut.conj k₀).toMonoidHom) hleft
    simpa only [Subgroup.map_sup,MonoidHom.map_zpowers,hk,f,conjugate_twice,
      map_top_of_surjective (MulAut.conj k₀).toMonoidHom (MulAut.conj k₀).surjective] using hh
  · have hh := congrArg (Subgroup.map (MulAut.conj k₀).toMonoidHom) hright
    simpa only [Subgroup.map_sup,MonoidHom.map_zpowers,ht,f,conjugate_twice,
      map_top_of_surjective (MulAut.conj k₀).toMonoidHom (MulAut.conj k₀).surjective] using hh

  · have hh := deleted_fixed_bot_conjugate _ hfixed k₀
    rw [Subgroup.map_sup,hJx] at hh
    simpa only [f,conjugate_twice] using hh

private theorem compatible_lifts_fixed {H : Type*} [Group H]
    (π : H →* S) (hs : Function.Surjective π) (E J C A : Subgroup H)
    (hC : C.map π = alternatingGroup (Fin 6)) (hkJ : π.ker ≤ J)
    (hJE : J ≤ E) (u : S)
    (hES : E.map π ≤ sylowCarrier.map (MulAut.conj u).toMonoidHom)
    (hE : Nat.card (E.map π) = 8) (hne : ¬ IsElementaryAbelian 2 (E.map π))
    (hJimage : J.map π = E.map π ⊓ (D 6).map (MulAut.conj u).toMonoidHom)
    (hmodel : IsConjugateTo (J.map π) plus ∨ IsConjugateTo (J.map π) (evenPart 6))
    (a : S) (ha : a ∈ A.map π) (hswap : a.IsSwap) :
    ∃ g y : H, y ∈ C ∧ y^3 ∈ π.ker ∧
      let J₁ := J.map (MulAut.conj g).toMonoidHom
      let A₁ := A.map (MulAut.conj y).toMonoidHom
      J₁ ⊔ A ⊔ A₁ = ⊤ ∧ y⁻¹ ∈ J₁ ⊔ J₁.map (MulAut.conj y⁻¹).toMonoidHom ∧
      E.map (MulAut.conj g).toMonoidHom ⊔ A = ⊤ ∧
      E.map (MulAut.conj g).toMonoidHom ⊔ A₁ = ⊤ ∧
      fixedSpace (deletedRepresentation (Fin 6))
        ((J₁ ⊔ J₁.map (MulAut.conj y⁻¹).toMonoidHom).map π) = ⊥ := by
  obtain ⟨v,b',hb,hbo,hgen,hpair,hleft,hright,hfixed⟩ :=
    compatible_pair_fixed (E.map π) (J.map π) u hES hE hne hJimage hmodel a hswap
  obtain ⟨g,hg⟩ := hs v
  have hbL : b' ∈ C.map π := hC.symm ▸ hb
  obtain ⟨y,hy,hyb⟩ := hbL
  let J₁ := J.map (MulAut.conj g).toMonoidHom
  let E₁ := E.map (MulAut.conj g).toMonoidHom
  let A₁ := A.map (MulAut.conj y).toMonoidHom
  have hJ : J₁.map π = (J.map π).map (MulAut.conj v).toMonoidHom := by
    rw [SylowCompatible.image_conjugate,hg]
  have hEE : E₁.map π = (E.map π).map (MulAut.conj v).toMonoidHom := by
    rw [SylowCompatible.image_conjugate,hg]
  have hker : π.ker.map (MulAut.conj g).toMonoidHom = π.ker :=
    mem_normalizer_iff_map_conj_eq.mp (by rw [normalizer_eq_top]; exact mem_top g)
  have hkJ₁ : π.ker ≤ J₁ := by rw [←hker]; exact map_mono hkJ
  have hA₁ : A₁.map π = (A.map π).map (MulAut.conj b').toMonoidHom := by
    rw [SylowCompatible.image_conjugate,hyb]
  have htop : J₁ ⊔ A ⊔ A₁ = ⊤ := by
    apply map_injective_of_ker_le π (hkJ₁.trans (le_sup_left.trans le_sup_left)) le_top
    rw [Subgroup.map_sup,Subgroup.map_sup,hJ,hA₁,map_top_of_surjective π hs]
    apply top_unique
    rw [←hgen]
    exact sup_le_sup (sup_le_sup_left (zpowers_le.mpr ha) _)
      (zpowers_le.mpr (mem_map_of_mem (MulAut.conj b').toMonoidHom ha))
  have hyP : y⁻¹ ∈ J₁ ⊔ J₁.map (MulAut.conj y⁻¹).toMonoidHom := by
    have hh : y⁻¹ ∈ ((J₁ ⊔ J₁.map (MulAut.conj y⁻¹).toMonoidHom).map π).comap π := by
      change π (y⁻¹) ∈ (J₁ ⊔ J₁.map (MulAut.conj y⁻¹).toMonoidHom).map π
      rw [Subgroup.map_sup,SylowCompatible.image_conjugate π J₁ y⁻¹,map_inv,hyb,hJ]
      exact hpair
    rwa [comap_map_eq,sup_eq_left.mpr (hkJ₁.trans le_sup_left)] at hh
  have hkE₁ : π.ker ≤ E₁ := hkJ₁.trans (map_mono hJE)
  have lift_gen (D : Subgroup H) (w : S) (hw : w ∈ D.map π)
      (hgen : (E.map π).map (MulAut.conj v).toMonoidHom ⊔ zpowers w = ⊤) :
      E₁ ⊔ D = ⊤ := by
    apply map_injective_of_ker_le π (hkE₁.trans le_sup_left) le_top
    rw [Subgroup.map_sup,hEE,map_top_of_surjective π hs]
    apply top_unique
    rw [←hgen]
    exact sup_le_sup_left (zpowers_le.mpr hw) _
  refine ⟨g,y,hy,?_,htop,hyP,lift_gen A a ha hleft,lift_gen A₁ ((MulAut.conj b') a) ?_ hright,?_⟩
  · rw [MonoidHom.mem_ker,map_pow,hyb]
    simpa only [hbo] using pow_orderOf_eq_one b'
  · rw [hA₁]
    exact mem_map_of_mem _ ha

  · rw [Subgroup.map_sup,SylowCompatible.image_conjugate π J₁ y⁻¹,map_inv,hyb,hJ]
    exact hfixed


universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

private theorem full_seed_fixed_of_image_deleted
    (s : FullSymmetricAction h e hz hn d) (hc : DistanceTwo.CentralLayer d)
    {z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical (alpha d.radical)) < 4)
    (P : Subgroup d.overgroup)
    (hP : fixedSpace (deletedRepresentation (Fin 6)) (P.map s.projection) = ⊥) :
    radiusSeed d ⊓ centralizer (P : Set d.overgroup) =
      radiusSeed d ⊓ centralizer ((⊤ : Subgroup d.overgroup) : Set d.overgroup) := by
  let := seed_elementary (h := h) (d := d)
  obtain ⟨j,hj,hcoords⟩ := full_seed_displacement_coordinates s hc p hsmall
  apply le_antisymm
  · rintro v ⟨hv,hvP⟩
    refine ⟨hv,?_⟩
    let w : Additive (radiusSeed d) := Additive.ofMul ⟨v,hv⟩
    obtain ⟨c,hc'⟩ := hcoords w
    have hfix : ∀ g ∈ P.map s.projection, seedAction s hc g w=w := by
      rintro g ⟨x,hx,rfl⟩
      apply Additive.toMul.injective
      apply Subtype.ext
      rw [seedAction_conjugate]
      change x*v*x⁻¹=v
      rw [hvP x hx,mul_inv_cancel_right]
    have hwhole := seed_fixed_of_deleted_fixed (seedAction s hc) j hj
      (P.map s.projection) hP w c hc' hfix
    intro x _
    have he := congrArg (fun y : Additive (radiusSeed d) => (y.toMul : d.overgroup))
      (hwhole (s.projection x))
    rw [seedAction_conjugate] at he
    exact mul_inv_eq_iff_eq_mul.mp he
  · exact inf_le_inf_left _ (centralizer_le (show P ≤ (⊤ : Subgroup d.overgroup) from le_top))

include e hz hn in
/-- The canonical paired selection retains both endpoint generation equations,
the same residual transporter, and the common fixed subgroup of the full seed. -/
theorem paired_generating_common_fixer_knownSimple
    (hne : ¬ IsElementaryAbelian 2
      (d.radical.map (SourceReduction.projection h e hz hn d)))
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 8)
    (hb : 2 < replacementDistance h d) (hmodel : EightSelection.ThreeDuadMover h e hz hn d)
    {z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical (alpha d.radical)) < 4) :
    ∃ g ∈ stabilizer d.radical (alpha d.radical),
      ∃ x ∈ Ltilde d.radical (alpha d.radical),
        x^3 ∈ Q d.radical (alpha d.radical) ∧
        let t := act d.radical g (beta d.radical)
        let J := EightEdgeComparison.edgeMover (d := d) (alpha d.radical) t
        Adjacent d.radical (alpha d.radical) t ∧
          J ⊔ Z d.radical z ⊔ Z d.radical (act d.radical x z) =
            stabilizer d.radical (alpha d.radical) ∧
          x ∈ J ⊔ J.map (MulAut.conj x).toMonoidHom ∧
          Q d.radical t ⊔ Z d.radical z = stabilizer d.radical (alpha d.radical) ∧
          Q d.radical t ⊔ Z d.radical (act d.radical x z) =
            stabilizer d.radical (alpha d.radical) ∧
          (Z d.radical (alpha d.radical) ⊓ centralizer (J : Set (FreeAmalgam d.radical))) ⊓
            centralizer (J.map (MulAut.conj x).toMonoidHom : Set (FreeAmalgam d.radical)) =
            Z d.radical (alpha d.radical) ⊓
              centralizer (stabilizer d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let J₀ := SmallMover.join (replacementMoved d) (pCore 2 d.overgroup) d.radical 4
  obtain ⟨u,hN,_,_,hJimage,_,_,_,_⟩ := EightMovers.radical_small_movers_knownSimple
    (e := e) (hz := hz) (hn := hn) hne hcard hb
  have hE : Nat.card (d.radical.map s.projection) = 8 := by
    rw [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
    exact hcard
  have hne' : ¬ IsElementaryAbelian 2 (d.radical.map s.projection) := by
    rw [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
    exact hne
  have hmodel' : IsConjugateTo (J₀.map s.projection) plus ∨
      IsConjugateTo (J₀.map s.projection) (evenPart 6) := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  have hkJ : s.projection.ker ≤ J₀ := by
    rw [s.projection_kernel]
    let := replacementMoved_normal h d
    exact SmallMover.kernel_le_join _ _ _ 4 (by decide) (replacement_core_le_radical h d)
      (by rw [←moved_centralizer s]; exact le_centralizer_iff.mpr le_rfl)
  obtain ⟨a,ha,hswap⟩ := small_critical_image_swap s hc p hsmall
  let A := (Z d.radical z).comap (embedM d.radical)
  obtain ⟨g,y,hy,hy3,htop,hpair,hleft,hright,hfixed⟩ := compatible_lifts_fixed s.projection s.surjective
    d.radical J₀ (replacementComponent d) A s.component_image hkJ
    (sSup_le fun _ hB => hB.1.1) u ((map_mono d.radical.le_normalizer).trans_eq hN)
    hE hne' hJimage hmodel' a ha hswap
  let J₁ := J₀.map (MulAut.conj g).toMonoidHom
  let A₁ := A.map (MulAut.conj y).toMonoidHom
  have hQ : (pCore 2 d.overgroup).map (MulAut.conj g).toMonoidHom = pCore 2 d.overgroup :=
    mem_normalizer_iff_map_conj_eq.mp (by rw [normalizer_eq_top]; exact mem_top g)
  have hU : (replacementMoved d).map (MulAut.conj g).toMonoidHom = replacementMoved d := by
    let := replacementMoved_normal h d
    exact mem_normalizer_iff_map_conj_eq.mp (by rw [normalizer_eq_top]; exact mem_top g)
  let f := (embedM d.radical g)⁻¹
  let x := (embedM d.radical y)⁻¹
  let t := act d.radical f (beta d.radical)
  let J := EightEdgeComparison.edgeMover (d := d) (alpha d.radical) t
  have hf : f ∈ stabilizer d.radical (alpha d.radical) := by
    change f ∈ stabilizer d.radical (mVertex d.radical 1)
    rw [stabilizer_m_base]
    exact ⟨g⁻¹,by simp only [map_inv,f]⟩
  have ht : Q d.radical t = (d.radical.map (MulAut.conj g).toMonoidHom).map (embedM d.radical) := by
    rw [Q_act,Q_beta,SylowCompatible.image_conjugate]
    simp only [f,inv_inv]
  have hJm : J₁.map (embedM d.radical) = J := by
    change ((SmallMover.join (replacementMoved d) (pCore 2 d.overgroup) d.radical 4).map
      (MulAut.conj g).toMonoidHom).map (embedM d.radical) = J
    rw [SmallMover.join_map _ (MulAut.conj g).injective,hU,hQ,
      SmallMover.join_map _ (embedM_injective d.radical),←hc.U_eq_moved,
      ←Q_alpha d.radical (replacement_radical_isPGroup h d) (replacement_core_le_radical h d),←ht]
  have hxL : x ∈ Ltilde d.radical (alpha d.radical) := by
    rw [Ltilde_alpha,replacement_residual h d]
    exact mem_map_of_mem _ ((replacementComponent d).inv_mem hy)
  have hAm : A.map (embedM d.radical) = Z d.radical z :=
    map_comap_eq_self ((critical_Z_le_stabilizer d.radical (replacementGeometry h d)
      (alpha d.radical) rfl (replacementDistance_pos h d) p.critical).trans_eq
        (stabilizer_m_base d.radical))
  have hA₁m : A₁.map (embedM d.radical) = Z d.radical (act d.radical x z) := by
    rw [SylowCompatible.image_conjugate,hAm,Z_act]
    simp only [x,inv_inv]
  have hrange : (embedM d.radical).range = stabilizer d.radical (alpha d.radical) :=
    (stabilizer_m_base d.radical).symm
  change y⁻¹ ∈ J₁ ⊔ J₁.map (MulAut.conj y⁻¹).toMonoidHom at hpair
  refine ⟨f,hf,x,hxL,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [s.projection_kernel] at hy3
    rw [Q_alpha d.radical (replacement_radical_isPGroup h d) (replacement_core_le_radical h d)]
    have hx3 : x^3=embedM d.radical ((y^3)⁻¹) := by simp only [x,inv_pow,map_inv,map_pow]
    rw [hx3]
    exact mem_map_of_mem _ ((pCore 2 d.overgroup).inv_mem hy3)
  · have hfix : act d.radical f (alpha d.radical)=alpha d.radical := hf
    rw [←hfix]
    exact (adjacent_act_iff d.radical f _ _).mpr (base_adjacent d.radical)
  · have hh := congrArg (Subgroup.map (embedM d.radical)) htop
    rwa [Subgroup.map_sup,Subgroup.map_sup,hJm,hAm,hA₁m,←MonoidHom.range_eq_map,
      hrange] at hh
  · have hh := mem_map_of_mem (embedM d.radical) hpair
    rwa [Subgroup.map_sup,SylowCompatible.image_conjugate (embedM d.radical) J₁ y⁻¹,
      map_inv,hJm] at hh
  · have hh := congrArg (Subgroup.map (embedM d.radical)) hleft
    rwa [Subgroup.map_sup,←ht,hAm,←MonoidHom.range_eq_map,hrange] at hh
  · have hh := congrArg (Subgroup.map (embedM d.radical)) hright
    rwa [Subgroup.map_sup,←ht,hA₁m,←MonoidHom.range_eq_map,hrange] at hh
  · have hPmap : (J₁ ⊔ J₁.map (MulAut.conj y⁻¹).toMonoidHom).map (embedM d.radical) =
        J ⊔ J.map (MulAut.conj x).toMonoidHom := by
      rw [Subgroup.map_sup,SylowCompatible.image_conjugate (embedM d.radical) J₁ y⁻¹,map_inv,hJm]
    have hmZ : (radiusSeed d).map (embedM d.radical) = Z d.radical (alpha d.radical) :=
      map_comap_eq_self ((Z_le_stabilizer d.radical _).trans_eq (stabilizer_m_base d.radical))
    have hfix := full_seed_fixed_of_image_deleted s hc p hsmall
      (J₁ ⊔ J₁.map (MulAut.conj y⁻¹).toMonoidHom) hfixed
    have hh := congrArg (Subgroup.map (embedM d.radical)) hfix
    rw [←map_inf_centralizer_of_injective _ (embedM_injective d.radical) (radiusSeed d)
        (J₁ ⊔ J₁.map (MulAut.conj y⁻¹).toMonoidHom),
      ←map_inf_centralizer_of_injective _ (embedM_injective d.radical) (radiusSeed d)
        (⊤ : Subgroup d.overgroup),hmZ,hPmap,
      ←MonoidHom.range_eq_map,hrange] at hh
    have hcentral : centralizer ((J ⊔ J.map (MulAut.conj x).toMonoidHom : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) =
        centralizer (J : Set (FreeAmalgam d.radical)) ⊓
          centralizer (J.map (MulAut.conj x).toMonoidHom : Set (FreeAmalgam d.radical)) := by
      apply le_antisymm
      · intro v hv
        exact ⟨fun j hj => hv j ((show J ≤ J ⊔ J.map (MulAut.conj x).toMonoidHom
          from le_sup_left) hj), fun j hj => hv j
            ((show J.map (MulAut.conj x).toMonoidHom ≤ J ⊔ J.map (MulAut.conj x).toMonoidHom
              from le_sup_right) hj)⟩
      · intro v hv
        have hvfix : J ⊔ J.map (MulAut.conj x).toMonoidHom ≤ centralizer ({v} : Set _) :=
          sup_le (fun j hj => mem_centralizer_singleton_iff.mpr (hv.1 j hj))
            (fun j hj => mem_centralizer_singleton_iff.mpr (hv.2 j hj))
        exact fun j hj => mem_centralizer_singleton_iff.mp (hvfix hj)
    rwa [hcentral,←inf_assoc] at hh

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.EightCompatible
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
