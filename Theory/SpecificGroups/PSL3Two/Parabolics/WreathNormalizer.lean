module
public import Theory.SpecificGroups.PSL3Two.Parabolics.ShearNormalizer
public import Theory.SpecificGroups.PSL3Two.Parabolics.WreathPair
public import Theory.GroupTheory.WreathTwoElementaryRank
public import Theory.GroupTheory.WeakClosureSylowTransport
public import Theory.GroupTheory.PCoreImage
/-!
# Normalizers and weak closure of the binary linear-three wreath radical

The two standard shears detect the line parabolic: if both conjugates lie
in the upper triangular subgroup, the conjugator preserves the line. The
small matrix certificate is applied coordinatewise in the wreath product.
The shear square is exactly the parabolic two-core, as its order is sixteen
and the parabolic quotient has order 72. Thus this literal core is weakly
closed in every ambient Sylow contained in the parabolic and has that
parabolic as its full normalizer.

The final theorem lifts both assertions through any two-group kernel with
a compatible parabolic marking. The Chapter14 source application supplies
this marking for its original outside H, rather than assuming weak closure.
Source: Aschbacher--Smith 14.6.16, printed p.1035; I.2.5 and I.5.4.
-/

public section
open Subgroup Representation BinaryLinearThree Matrix
open Theory.GroupTheory.WreathTwoElementaryRank
namespace Matrix.PSL3Two.WreathPair

set_option maxRecDepth 10000 in
private theorem shear_test : ∀ g : SL,
    g * shear (Multiplicative.ofAdd (1,0)) * g⁻¹ ∈ borelSL →
    g * shear (Multiplicative.ofAdd (0,1)) * g⁻¹ ∈ borelSL →
    g ∈ lineParabolicSL := by
  decide +kernel

private def radical : Subgroup Actor := (R.prod R).map baseHom

private theorem mem_radical (w : Actor) : w ∈ radical ↔ w.right = 1 ∧ ∀ i, w.left i ∈ R := by
  constructor
  · rintro ⟨⟨x,y⟩,⟨hx,hy⟩,rfl⟩
    refine ⟨rfl,fun i => ?_⟩
    change (if i = 1 then x else y) ∈ R
    split_ifs
    · exact hx
    · exact hy
  · rintro ⟨hr,hl⟩
    refine ⟨(w.left 1,w.left turn),⟨hl 1,hl turn⟩,?_⟩
    apply RegularWreathProduct.ext
    · funext i
      rcases index_cases i with rfl | rfl <;> simp [baseHom,turn_ne_one]
    · exact hr.symm

private theorem radical_le_borel : radical ≤ borel := by
  intro w hw i
  obtain ⟨_,hi⟩ := (mem_radical w).mp hw
  obtain ⟨c,hc⟩ := hi i
  rw [←hc,mem_borelSL_iff]
  exact ⟨rfl,rfl,rfl⟩

private theorem line_normalizes_radical : line ≤ normalizer (radical : Set Actor) := by
  apply le_normalizer_iff.mpr
  intro g hg w hw
  obtain ⟨hr,hi⟩ := (mem_radical w).mp hw
  apply (mem_radical _).mpr
  refine ⟨by simp [hr],fun i => ?_⟩
  have hn : g.left i ∈ normalizer (R : Set SL) := normalizer_shear_radical.symm ▸ hg i
  have hh := (mem_normalizer_iff.mp hn (w.left (g.right⁻¹ * i))).mp (hi _)
  simpa [hr,mul_assoc] using hh

private theorem radical_card : Nat.card radical = 16 := by
  rw [radical,card_map_of_injective baseHom_injective,
    Nat.card_congr (prodEquiv R R).toEquiv,Nat.card_prod,BinaryLinearThree.card_R]

private theorem radical_two : IsPGroup 2 radical := IsPGroup.of_card (n := 4) radical_card

private theorem radical_eq_core : radical = line.pCoreIn 2 := by
  apply eq_of_le_of_card_ge
  · exact le_pCoreIn_of_normalizes radical_two (radical_le_borel.trans borel_le_line)
      line_normalizes_radical
  · have hline : Nat.card line = 1152 := by
      rw [Nat.card_congr lineEquiv.toEquiv,RegularWreathProduct.card,Nat.card_perm]
      norm_num [Bit,Nat.card_eq_fintype_card,Nat.factorial]
    have hquot : Nat.card (line ⧸ pCore 2 line) = 72 := by
      rw [Nat.card_congr lineQuotientEquiv.toEquiv]
      rw [RegularWreathProduct.card]
      have h : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) = 6 := by
        rw [Nat.card_eq_fintype_card]
        decide +kernel
      rw [h]
      norm_num [Nat.card_eq_fintype_card]
    have hh := (pCore 2 line).card_mul_index
    rw [index_eq_card,hquot,hline] at hh
    rw [pCoreIn,card_map_of_injective line.subtype_injective,radical_card]
    omega

private theorem radical_fusion_test (g : Actor)
    (hg : radical.map (MulAut.conj g).toMonoidHom ≤ borel) : g ∈ line := by
  intro i
  apply shear_test
  · let r := shear (Multiplicative.ofAdd (1,0))
    let w : Actor := ⟨fun _ => r,1⟩
    have hw : w ∈ radical := (mem_radical w).mpr ⟨rfl,fun _ => ⟨_,rfl⟩⟩
    have hh := hg (mem_map_of_mem (MulAut.conj g).toMonoidHom hw) i
    simpa [w,MulAut.conj_apply,mul_assoc] using hh
  · let r := shear (Multiplicative.ofAdd (0,1))
    let w : Actor := ⟨fun _ => r,1⟩
    have hw : w ∈ radical := (mem_radical w).mpr ⟨rfl,fun _ => ⟨_,rfl⟩⟩
    have hh := hg (mem_map_of_mem (MulAut.conj g).toMonoidHom hw) i
    simpa [w,MulAut.conj_apply,mul_assoc] using hh

/-- The line-wreath radical has the full parabolic as its normalizer. -/
theorem line_core_normalizer : normalizer (line.pCoreIn 2 : Set Actor) = line := by
  rw [←radical_eq_core]
  apply le_antisymm _ line_normalizes_radical
  intro g hg
  apply radical_fusion_test
  exact (mem_normalizer_iff_map_conj_eq.mp hg).le.trans radical_le_borel

/-- The literal line-wreath core is weakly closed in every ambient Sylow
contained in that parabolic. -/
theorem line_core_weakly_closed (T : Sylow 2 Actor) (hT : (T : Subgroup Actor) ≤ line)
    (g : Actor) (hg : (line.pCoreIn 2).map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup Actor)) :
    (line.pCoreIn 2).map (MulAut.conj g).toMonoidHom = line.pCoreIn 2 := by
  have hcT : line.pCoreIn 2 ≤ (T : Subgroup Actor) := by
    have hh := pCoreIn_le_sylow line (T.subtype hT)
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hT] using hh
  apply SubgroupFusion.weakly_closed_in_p_overgroup_of_one_sylow sylow
    (line.pCoreIn 2) (T : Subgroup Actor) hcT T.isPGroup' _ g hg
  intro x hx
  rw [←radical_eq_core] at hx ⊢
  exact mem_normalizer_iff_map_conj_eq.mp (line_normalizes_radical (radical_fusion_test x (by simpa only [Subgroup.conjBy,sylow_eq] using hx)))

variable {G : Type*} [Group G] [Finite G]

/-- A compatible line-parabolic marking lifts the actual core normalizer
and weak closure through the given two-group kernel. -/
theorem cover_core_normalizer (f : G →* Actor) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) (T : Sylow 2 G) (B : Subgroup G)
    (hTB : (T : Subgroup G) ≤ B) (hB : B.map f = line) :
    normalizer (B.pCoreIn 2 : Set G) = B ∧
      ∀ g : G, (B.pCoreIn 2).map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G) →
        (B.pCoreIn 2).map (MulAut.conj g).toMonoidHom = B.pCoreIn 2 := by
  have hkerB : f.ker ≤ B := (hk.le_sylow_of_normal T).trans hTB
  have hkerC : f.ker ≤ B.pCoreIn 2 := le_pCoreIn_of_normalizes hk hkerB
    (by simp [normalizer_eq_top])
  have hmap : (B.pCoreIn 2).map f = line.pCoreIn 2 := by
    rw [map_pCoreIn_of_ker_isPGroup f hk B,hB]
  have hn : normalizer ((B.pCoreIn 2).map f : Set Actor) = B.map f := by
    rw [hmap,hB,line_core_normalizer]
  have hn' := congrArg (comap f) hn
  rw [comap_normalizer_eq_of_surjective _ hf,comap_map_eq_self hkerC,
    comap_map_eq_self hkerB] at hn'
  refine ⟨hn',?_⟩
  intro g hg
  have hconj (A : Subgroup G) :
      (A.map (MulAut.conj g).toMonoidHom).map f =
        (A.map f).map (MulAut.conj (f g)).toMonoidHom := by
    rw [Subgroup.map_map,Subgroup.map_map]
    congr 1
    apply MonoidHom.ext
    intro x
    simp only [MonoidHom.comp_apply,MulEquiv.toMonoidHom_eq_coe,MulAut.conj_apply,
      MonoidHom.coe_coe,map_mul,map_inv]
  have hT : (T.mapSurjective hf : Subgroup Actor) ≤ line := hB ▸ map_mono hTB
  have hle : (line.pCoreIn 2).map (MulAut.conj (f g)).toMonoidHom ≤
      (T.mapSurjective hf : Subgroup Actor) := by
    rw [←hmap,←hconj]
    exact map_mono hg
  have he := line_core_weakly_closed (T.mapSurjective hf) hT (f g) hle
  rw [←hmap,←hconj] at he
  have hkerCg : f.ker ≤ (B.pCoreIn 2).map (MulAut.conj g).toMonoidHom := by
    have hn : f.ker.map (MulAut.conj g).toMonoidHom = f.ker :=
      mem_normalizer_iff_map_conj_eq.mp (show g ∈ normalizer (f.ker : Set G) by
        simp only [normalizer_eq_top,mem_top])
    exact hn ▸ map_mono hkerC
  have hh := congrArg (comap f) he
  rwa [comap_map_eq_self hkerCg,comap_map_eq_self hkerC] at hh
end Matrix.PSL3Two.WreathPair
