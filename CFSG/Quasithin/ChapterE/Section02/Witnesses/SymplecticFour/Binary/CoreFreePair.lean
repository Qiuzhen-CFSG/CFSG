module
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.SymplecticFour.Binary.FullAction
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.QuotientLift.Source
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.BenderPlacement.OriginalModels
public import Theory.SpecificGroups.SymmetricSix.CoreFreeSylowOvergroups
/-!
# The binary symplectic conjugate pair

For the original minimal parabolic, the marked elementary four in Aut(A₆)
constructs the literal two-conjugate subgroup S₆. Its prescribed Sylow
intersection centralizes that four, and every proper full-Sylow overgroup in
S₆ has trivial normal core. This yields the actual Sp₄(2) quotient required by
GLS, *The Classification of the Finite Simple Groups*, Vol. II, E.2.7–9
(printed pp. 219–222), preserving the original pair and quotient maps.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterE.Witnesses.SymplecticFour.Binary
open AlternatingSix.ShadowLocal
open AlternatingSix.ShadowLocal.Identification
open AlternatingSix.ShadowLocal.BinaryWitness
open Theory.SpecificGroups.SymmetricSix.CentralFourPair
local notation "Sp2" => Theory.SpecificGroups.SymplecticFour.Sp (ZMod 2)

private theorem natural_sup_sylow (P : Sylow 2 AutA6) : natural ⊔ (P : Subgroup AutA6) = ⊤ := by
  let A := natural ⊔ (P : Subgroup AutA6)
  have h1 : 720 ∣ Nat.card A := card_natural ▸ card_dvd_of_le (show natural ≤ A from le_sup_left)
  have h2 : 32 ∣ Nat.card A := sylow_card P ▸ card_dvd_of_le (show (P : Subgroup AutA6) ≤ A from le_sup_right)
  have hd : 1440 ∣ Nat.card A := by
    have hh := Nat.lcm_dvd h1 h2
    norm_num [Nat.lcm] at hh
    exact hh
  exact eq_of_le_of_card_ge (show A ≤ ⊤ from le_top) (by
    rw [card_top,card_aut]
    exact Nat.le_of_dvd Nat.card_pos hd)

private theorem map_conjugate {G D : Type*} [Group G] [Group D]
    (A : Subgroup G) (g:G) (f:G→*D) :
    (A.map (MulAut.conj g).toMonoidHom).map f =
      (A.map f).map (MulAut.conj (f g)).toMonoidHom := by
  rw [map_map,map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulAut.conj_apply,map_mul,map_inv]

variable {G : Type*} [Group G] [Finite G]

/-- The central-four marking constructs an actual E.2.4 pair, with the original
Sylow intersection, trivial relative core and literal binary Sp4 model. -/
theorem pair_of_marked_aut
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (V : Subgroup G) (hVT : V ≤ (T : Subgroup G))
    (e : G ≃* AutA6) (P : Sylow 2 AutA6)
    (hT : (T : Subgroup G).map e.toMonoidHom = (P : Subgroup AutA6))
    (hV : V.map e.toMonoidHom = markedFour P) :
    ∃ w : QuotientLift.Pair T (ChapterB.minimalParabolicMax T hP) V,
    ∃ ξ : (w.subgroup ⧸ ((ChapterB.minimalParabolicMax T hP).subgroupOf w.subgroup).normalCore) ≃* Sp2,
    ∃ S : Sylow 2 Sp2,
      (V.subgroupOf w.subgroup).map (ξ.toMonoidHom.comp (QuotientGroup.mk' _)) ≤
        (center S).map (S : Subgroup Sp2).subtype := by
  classical
  let c := MulAut.conj (conjugatingPermutation P)
  let j : Equiv.Perm (Fin 6) →* G := e.symm.toMonoidHom.comp (permutationAction.comp c.toMonoidHom)
  have hj : Function.Injective j := e.symm.injective.comp (permutationAction_injective.comp c.injective)
  have hej : e.toMonoidHom.comp j = permutationAction.comp c.toMonoidHom := by
    apply MonoidHom.ext
    intro x
    exact e.apply_symm_apply _
  let I := j.range
  have hImap : I.map e.toMonoidHom = natural := by
    change j.range.map e.toMonoidHom = _
    rw [←MonoidHom.range_comp,hej,MonoidHom.range_comp,
      MonoidHom.range_eq_top.mpr c.surjective,←MonoidHom.range_eq_map]
    rfl
  have hIj : four.map j = V := by
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [map_map,hej,←markedFour_eq_permutation_pair,hV]
  have hVI : V ≤ I := by rw [←hIj]; exact map_le_range _ _
  have hInorm : I.Normal := by
    have hn : natural.Normal := normal_of_index_eq_two
      GLS3.Chapter5.naturalAlternatingAutomorphismSubgroup_index
    have hi : I = natural.comap e.toMonoidHom := by
      rw [←hImap,comap_map_eq,(MonoidHom.ker_eq_bot_iff e.toMonoidHom).mpr e.injective,sup_bot_eq]
    rw [hi]
    infer_instance
  let := hInorm
  obtain ⟨S,hS⟩ := T.exists_subgroupOf_eq_of_normal I
  have hSmap : (S : Subgroup I).map I.subtype = (T : Subgroup G) ⊓ I := by
    rw [hS,subgroupOf_map_subtype]
  let g : I := ⟨j opposite,⟨opposite,rfl⟩⟩
  have hgen : V.subgroupOf I ⊔ (V.subgroupOf I).map (MulAut.conj g).toMonoidHom = ⊤ := by
    apply map_injective I.subtype_injective
    rw [Subgroup.map_sup,map_conjugate,map_subgroupOf_eq_of_le hVI,
      ←MonoidHom.range_eq_map,range_subtype]
    have hh := congrArg (map j) pair_generates
    rw [Subgroup.map_sup,map_conjugate,hIj,←MonoidHom.range_eq_map] at hh
    exact hh
  have hIT : I ⊔ (T : Subgroup G) = ⊤ := by
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [Subgroup.map_sup,hImap,hT,natural_sup_sylow,map_top_of_surjective _ e.surjective]
  let M := ChapterB.minimalParabolicMax T hP
  let A := M.subgroupOf I
  have hSA : (S : Subgroup I) ≤ A := by
    rw [hS]
    exact fun x hx => (ChapterB.minimalParabolicMax_spec T hP).2 hx
  have hA : A ≠ ⊤ := by
    intro ha
    have hi : I ≤ M := subgroupOf_eq_top.mp ha
    have hg : (⊤ : Subgroup G) ≤ M := by
      rw [←hIT]
      exact sup_le hi (ChapterB.minimalParabolicMax_spec T hP).2
    exact (ChapterB.minimalParabolicMax_spec T hP).1.ne_top (top_unique hg)
  let η₀ : I ≃* Equiv.Perm (Fin 6) := (MonoidHom.ofInjective hj).symm
  have hc : A.normalCore = ⊥ :=
    Theory.SpecificGroups.SymmetricSix.normalCore_eq_bot_of_sylow_le η₀ S A hSA hA
  have htclosed : ∃ Q : Sylow 2 A.normalCore, (Q : Subgroup A.normalCore).Normal := by
    rw [hc]
    exact ⟨default,inferInstance⟩
  let w : QuotientLift.Pair T M V := ⟨I,hVI,g,hgen,S,hSmap,htclosed⟩
  let η : I ≃* Sp2 := η₀.trans Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv
  let ξ : (I ⧸ A.normalCore) ≃* Sp2 := (BenderPlacement.coreFreeQuotientEquiv A hc).trans η
  let Q := S.mapSurjective (f := η.toMonoidHom) η.surjective
  refine ⟨w,ξ,Q,?_⟩
  rintro _ ⟨v,hv,rfl⟩
  change η v ∈ (center Q).map (Q : Subgroup Sp2).subtype
  have hvS : v ∈ (S : Subgroup I) := by rw [hS]; exact hVT hv
  let vS : S := ⟨v,hvS⟩
  have hvC : vS ∈ center S := by
    apply mem_center_iff.mpr
    intro s
    apply Subtype.ext
    apply Subtype.ext
    apply e.injective
    have hvm : e (v:G) ∈ markedFour P := hV ▸ mem_map_of_mem e.toMonoidHom hv
    have hsm : e ((s:I):G) ∈ (P : Subgroup AutA6) ⊓ natural := by
      refine ⟨?_,?_⟩
      · rw [←hT]
        exact mem_map_of_mem _ (show ((s:I):G) ∈ T from by have hh : (s:I) ∈ (S : Subgroup I) := s.property; rw [hS] at hh; exact hh)
      · rw [←hImap]
        exact mem_map_of_mem _ (s:I).property
    change e (((s:I):G) * (v:G)) = e ((v:G) * ((s:I):G))
    rw [map_mul,map_mul]
    exact markedFour_centralizes_natural_intersection P hvm _ hsm
  let f : S ≃* Q := η.subgroupMap (S : Subgroup I)
  refine ⟨f vS,?_,rfl⟩
  exact (centerCongr f ⟨vS,hvC⟩).property
end CFSG.Quasithin.ChapterE.Witnesses.SymplecticFour.Binary
