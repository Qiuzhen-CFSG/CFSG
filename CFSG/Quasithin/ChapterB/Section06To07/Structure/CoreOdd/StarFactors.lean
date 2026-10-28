module

public import CFSG.Quasithin.ChapterB.Section06To07.Structure.CoreOdd.Nonsolvable
public import Theory.GroupTheory.GeneralizedFitting.ComponentLocalClosure.Orbit

/-!
# Transitive simple factors in the star quotient of a minimal parabolic

For a nonsolvable minimal parabolic `H`, let `J` be the core of its unique
maximal overgroup of `T`. The residual `R = O²(H/J)` is a nonabelian minimal
normal subgroup. Choose an actual component of `R`; chief-component theory
makes it nonabelian simple and a component of `H/J`. The residual normalizes
each of its components. Consequently the join of the component's conjugates
under the actual Sylow image `T*` is normalized by both `R` and `T*`. Since
`H/J = R T*`, chief minimality makes that orbit join equal to `R`.

The product is indexed by distinct conjugate subgroups, retaining the literal
conjugation maps and their transitive action. Distinct components commute;
their trivial centers imply independence from the entire complementary join.
The canonical product homomorphism is injective with range `R`, and on each
single coordinate it is the original subgroup inclusion into `H/J`.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, B.6.8(3), printed pp.113–115. This proves the
transitive simple-factor assertion. The local normalizer and automizer
assertions are separate arguments.
-/

public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterB
variable {H : Type*} [Group H] [Finite H]

/-- B.6.8(3): an actual nonabelian simple component of `H/J` has its
`T*`-conjugates generate the star residual. All premises are discharged from
the original minimal-parabolic data and nonsolvability of `H`. -/
theorem minimalParabolic_nonsolvable_star_factor (T : Sylow 2 H) (hP : IsMinimalParabolicOver T ⊤)
    (hs : ¬ Group.IsSolvable H) :
    ∃ L : Subgroup (minimalParabolicStarQuotient T hP),
      L ≤ pResidual 2 (minimalParabolicStarQuotient T hP) ∧
      IsSimpleGroup L ∧ ¬ IsMulCommutative L ∧
      IsComponent (minimalParabolicStarQuotient T hP) L ∧
      componentOrbit L (minimalParabolicStarSylow T hP) =
        pResidual 2 (minimalParabolicStarQuotient T hP) := by
  classical
  let G := minimalParabolicStarQuotient T hP
  let R : Subgroup G := pResidual 2 G
  let A : Subgroup G := minimalParabolicStarSylow T hP
  have hchief := minimalParabolic_star_residual_chief T hP
  have hna := minimalParabolic_nonsolvable_star_residual_nonabelian T hP hs
  have hlayer := minimalParabolic_nonsolvable_star_layer T hP hs
  have hex : ∃ K : Subgroup R, IsComponent R K := by
    by_contra! hn
    have hb : componentLayer R ≤ ⊥ := sSup_le fun K hK => (hn K hK).elim
    rw [hlayer] at hb
    apply (ne_of_gt hchief.lt)
    apply bot_unique
    intro r hr
    have hm : (⟨r, hr⟩ : R) ∈ (⊥ : Subgroup R) := hb (mem_top _)
    exact congrArg Subtype.val hm
  obtain ⟨K, hK⟩ := hex
  let L := K.map R.subtype
  have hLR : L ≤ R := map_subtype_le K
  have hLin : IsComponentIn L R := by
    refine ⟨hLR, ?_⟩
    have he : L.subgroupOf R = K :=
      comap_map_eq_self (by rw [R.ker_subtype]; exact bot_le)
    rwa [he]
  have hL : IsComponent G L :=
    ⟨hLin.2.1.trans hLR (inferInstance : R.Normal).isSubnormal, hLin.quasisimple⟩
  have hsimple : IsSimpleGroup L := hchief.component_isSimple hna hLin
  let := hsimple
  have hLna : ¬ IsMulCommutative L := by
    let := hL.2
    exact Group.IsPerfect.not_isMulCommutative L
  have hconj (a : A) : L.map (MulAut.conj (a : G)).toMonoidHom ≤ R := by
    calc
      _ ≤ R.map (MulAut.conj (a : G)).toMonoidHom := map_mono hLR
      _ = R := (normal_iff_map_conj_eq.mp (inferInstance : R.Normal)) a
  have hnorm (C : Subgroup G) (hCR : C ≤ R) (hC : IsComponent G C) :
      R ≤ normalizer (C : Set G) := by
    apply hchief.le_of_components_le hna
    intro D hD
    by_cases he : D = C
    · exact he ▸ C.le_normalizer
    · exact (commutator_eq_bot_iff_le_centralizer.mp
        (hD.commutator_eq_bot_of_ne ⟨hCR, hC.subgroupOf hCR⟩ he)).trans
          (Subgroup.centralizer_le_normalizer _)
  have hRN : R ≤ normalizer (componentOrbit L A : Set G) :=
    (le_iInf fun a : A => hnorm _ (hconj a) (hL.map_conj a)).trans
      (iInf_normalizer_le_normalizer_iSup _)
  have hOn : (componentOrbit L A).Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    rw [← minimalParabolic_residual_star_sup_sylow T hP]
    exact sup_le hRN (le_normalizer_componentOrbit L A)
  have horbit : componentOrbit L A = R := by
    obtain he | he := hchief.minimal _ hOn bot_le (iSup_le hconj)
    · exact False.elim (hLin.ne_bot (bot_unique ((le_componentOrbit L A).trans he.le)))
    · exact he
  exact ⟨L, hLR, hsimple, hLna, hL, horbit⟩

/-- Distinct actual conjugates under the Sylow image in the literal star quotient. -/
abbrev MinimalParabolicStarFactorIndex (T : Sylow 2 H) (hP : IsMinimalParabolicOver T ⊤)
    (L : Subgroup (minimalParabolicStarQuotient T hP)) :=
  {C : Subgroup (minimalParabolicStarQuotient T hP) //
    ∃ a : (minimalParabolicStarSylow T hP),
      L.map (MulAut.conj (a : minimalParabolicStarQuotient T hP)).toMonoidHom = C}

/-- The factors are transitively conjugate by elements of the actual Sylow
image, with a transporter in that Sylow subgroup. -/
theorem MinimalParabolicStarFactorIndex.transitive (T : Sylow 2 H) (hP : IsMinimalParabolicOver T ⊤)
    (L : Subgroup (minimalParabolicStarQuotient T hP)) (i j : MinimalParabolicStarFactorIndex T hP L) :
    ∃ a : (minimalParabolicStarSylow T hP),
      i.val.map (MulAut.conj (a : minimalParabolicStarQuotient T hP)).toMonoidHom = j.val := by
  obtain ⟨a, ha⟩ := i.property
  obtain ⟨b, hb⟩ := j.property
  refine ⟨b * a⁻¹, ?_⟩
  rw [← ha, ← hb, map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

/-- The full direct-product assertion in B.6.8(3), applied to the original
minimal parabolic. The indices are distinct actual `T*`-conjugates; every
factor is nonabelian simple and an ambient component. `iSupIndep` asserts
disjointness of each factor from the join of all other factors. The product
map has range exactly the star residual and preserves every factor inclusion. -/
theorem minimalParabolic_nonsolvable_star_factor_product (T : Sylow 2 H) (hP : IsMinimalParabolicOver T ⊤)
    (hs : ¬ Group.IsSolvable H) :
    ∃ L : Subgroup (minimalParabolicStarQuotient T hP),
      L ≤ pResidual 2 (minimalParabolicStarQuotient T hP) ∧
      IsSimpleGroup L ∧ ¬ IsMulCommutative L ∧
      IsComponent (minimalParabolicStarQuotient T hP) L ∧
      componentOrbit L (minimalParabolicStarSylow T hP) =
        pResidual 2 (minimalParabolicStarQuotient T hP) ∧
      (∀ i : MinimalParabolicStarFactorIndex T hP L,
        IsSimpleGroup i.val ∧ ¬ IsMulCommutative i.val ∧
          IsComponent (minimalParabolicStarQuotient T hP) i.val) ∧
      (Pairwise fun i j : MinimalParabolicStarFactorIndex T hP L =>
        ∀ x y : minimalParabolicStarQuotient T hP,
          x ∈ i.val → y ∈ j.val → Commute x y) ∧
      iSupIndep (fun i : MinimalParabolicStarFactorIndex T hP L => i.val) ∧
      (⨆ i : MinimalParabolicStarFactorIndex T hP L, i.val) =
        pResidual 2 (minimalParabolicStarQuotient T hP) ∧
      (letI := Classical.decEq (MinimalParabolicStarFactorIndex T hP L)
       ∃ f : (∀ i : MinimalParabolicStarFactorIndex T hP L, i.val) →*
           minimalParabolicStarQuotient T hP,
         Function.Injective f ∧
         f.range = pResidual 2 (minimalParabolicStarQuotient T hP) ∧
         ∀ (i : MinimalParabolicStarFactorIndex T hP L) (x : i.val),
           f (Pi.mulSingle i x) = (x : minimalParabolicStarQuotient T hP)) := by
  classical
  obtain ⟨L, hLR, hsimple, hnaL, hL, horbit⟩ := minimalParabolic_nonsolvable_star_factor T hP hs
  let G := minimalParabolicStarQuotient T hP
  let R : Subgroup G := pResidual 2 G
  let A : Subgroup G := minimalParabolicStarSylow T hP
  let I := MinimalParabolicStarFactorIndex T hP L
  have hchief := minimalParabolic_star_residual_chief T hP
  have hna := minimalParabolic_nonsolvable_star_residual_nonabelian T hP hs
  have hi (i : I) : IsComponent G i.val := by
    obtain ⟨a, ha⟩ := i.property
    rw [← ha]
    exact hL.map_conj a
  have hin (i : I) : IsComponentIn i.val R := by
    have hle : i.val ≤ R := by
      obtain ⟨a, ha⟩ := i.property
      rw [← ha]
      exact (le_iSup (fun a : A => L.map (MulAut.conj (a : G)).toMonoidHom) a).trans
        horbit.le
    exact ⟨hle, (hi i).subgroupOf hle⟩
  have hcenter (i : I) : center i.val = ⊥ := hchief.component_center_eq_bot hna (hin i)
  have hcomm : Pairwise fun i j : I =>
      ∀ x y : G, x ∈ i.val → y ∈ j.val → Commute x y := by
    intro i j hij x y hx hy
    have hc := (hi i).commutator_eq_bot_of_ne (hi j) (fun he => hij (Subtype.ext he))
    exact (mem_centralizer_iff.mp ((commutator_eq_bot_iff_le_centralizer.mp hc) hx) y hy).symm
  have hind : iSupIndep (fun i : I => i.val) :=
    iSupIndep_of_centerless_of_pairwise_commute _ hcenter hcomm
  have hjoin : (⨆ i : I, i.val) = R := by
    change (⨆ i : I, i.val) = pResidual 2 (minimalParabolicStarQuotient T hP)
    rw [← horbit]
    apply le_antisymm
    · apply iSup_le
      rintro ⟨C, a, rfl⟩
      exact le_iSup (fun a : A => L.map (MulAut.conj (a : G)).toMonoidHom) a
    · exact iSup_le fun a => le_iSup (fun i : I => i.val) ⟨_, a, rfl⟩
  refine ⟨L, hLR, hsimple, hnaL, hL, horbit, ?_, hcomm, hind, hjoin, ?_⟩
  · intro i
    have hsi := hchief.component_isSimple hna (hin i)
    let := hsi
    let := (hi i).2
    exact ⟨hsi, Group.IsPerfect.not_isMulCommutative i.val, hi i⟩
  · let : Fintype I := Fintype.ofFinite I
    let : DecidableEq I := Classical.decEq I
    let f : (∀ i : I, i.val) →* G := noncommPiCoprod hcomm
    exact ⟨f, injective_noncommPiCoprod_of_iSupIndep hind,
      noncommPiCoprod_range.trans hjoin, fun i x => noncommPiCoprod_mulSingle i x⟩

end CFSG.Quasithin.ChapterB

end
