module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.PathBorel
public import Theory.SpecificGroups.Dihedral.FourthPowerAutomorphisms
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
public import Theory.SpecificGroups.SL2.TwoCoreBorel

/-!
# The dihedral middle case of the path Borel image

An actor fixing a dihedral edge induces a D₁₀ automorphism fixing its
marked reflection. Its fourth power acts trivially on the local quotient,
so it normalizes every edge Sylow and fixes every neighbor. Consequently
the path image contains fourth powers of the entire beta Borel. The middle
core supplies the beta Sylow, and fourth powers cover the odd diagonal
quotient, proving that the path image is the whole Borel.

All actions, cores and quotient maps are the original ones; no double
transitivity is assigned to D₁₀. Source: DGS, *Groups and Graphs* (1985),
8.5, printed p.139, the two-edge path actor.
-/

@[expose] public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- The fourth power of a full edge actor fixes every neighbor of its dihedral endpoint. -/
theorem source_dihedral_edge_fourth_fixes_neighbors (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {v w z : Vertex (family P)} (hvw : (graph (family P)).Adj v w)
    (hvz : (graph (family P)).Adj v z)
    (e : (d.localGroup v ⧸ pCore 2 (d.localGroup v)) ≃* DihedralGroup 5)
    (t : G) (ht : t ∈ stabilizer (family P) v ⊓ stabilizer (family P) w) :
    t ^ 4 ∈ stabilizer (family P) z := by
  let := finite_endpoints h
  let L := d.localGroup v
  let : Finite L := Finite.of_injective (inclusion (d.local_le v)) (inclusion_injective _)
  have htN : t ∈ normalizer (L : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    exact (d.conjugate t v).symm.trans (congrArg d.localGroup ht.1)
  let tN : normalizer (L : Set G) := ⟨t,htN⟩
  let f := (quotientAut (pCore 2 L)).comp L.normalizerMonoidHom
  let α := (MulAut.congr e).toMonoidHom.comp f
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq (x : L) : q (L.normalizerMonoidHom tN x) = α tN (q x) := by
    change e (QuotientGroup.mk' (pCore 2 L) (L.normalizerMonoidHom tN x)) =
      e ((quotientAut (pCore 2 L) (L.normalizerMonoidHom tN))
        (e.symm (e (QuotientGroup.mk' (pCore 2 L) x))))
    rw [e.symm_apply_apply,quotientAut_apply_mk]
  obtain ⟨R,hR⟩ := source_edge_core_local_sylow h hB d hvw
  have htR : t ∈ normalizer ((R : Subgroup L).map L.subtype : Set G) :=
    ((source_edge_local_normalizer h d hvw (.dihedral ⟨e⟩) R hR).1.ge ht).2
  let T := R.mapSurjective (f := q) (e.surjective.comp (QuotientGroup.mk'_surjective _))
  have hcard : Nat.card T = 2 := by
    rw [T.card_eq_multiplicity,DihedralGroup.nat_card]
    rw [Nat.factorization_mul (by decide) (by decide),
      Nat.prime_two.factorization,Nat.prime_five.factorization]
    norm_num
  have hinv (s : DihedralGroup 5) (hs : s ∈ T) : α tN s ∈ T := by
    obtain ⟨r,hr,rfl⟩ := hs
    rw [←hq]
    apply mem_map_of_mem q
    have hm := (mem_normalizer_iff.mp htR (r : G)).mp (mem_map_of_mem L.subtype hr)
    obtain ⟨u,hu,heu⟩ := hm
    exact (show u = L.normalizerMonoidHom tN r from Subtype.ext heu) ▸ hu
  obtain ⟨s,hs1,hs⟩ := (Nat.card_eq_two_iff' (1 : T)).mp hcard
  have hs1' : (s : DihedralGroup 5) ≠ 1 := by
    intro he
    exact hs1 (Subtype.ext he)
  have hsq : (s : DihedralGroup 5) ^ 2 = 1 := by
    have he := pow_card_eq_one' (x := s)
    change s ^ Nat.card (T : Subgroup (DihedralGroup 5)) = 1 at he
    rw [hcard] at he
    exact congrArg Subtype.val he
  have hfix : α tN (s : DihedralGroup 5) = s := by
    exact congrArg Subtype.val (hs ⟨_,hinv s s.property⟩ (by
      intro he
      exact hs1' ((α tN).map_eq_one_iff.mp (congrArg Subtype.val he))))
  have he : f (tN ^ 4) = 1 := by
    apply (MulAut.congr e).injective
    rw [map_one]
    change α (tN ^ 4) = 1
    rw [map_pow]
    exact DihedralGroup.fourth_pow_eq_one_of_fixed_involution (α tN) s hsq hs1' hfix
  obtain ⟨S,hS⟩ := source_edge_core_local_sylow h hB d hvz
  let q₀ := QuotientGroup.mk' (pCore 2 L)
  have hq₀ (x : L) : q₀ (L.normalizerMonoidHom (tN ^ 4) x) = q₀ x := by
    have hh := DFunLike.congr_fun he (q₀ x)
    simpa only [f,MonoidHom.comp_apply,q₀,quotientAut_apply_mk,MulAut.one_apply] using hh
  have hNS : t ^ 4 ∈ normalizer ((S : Subgroup L).map L.subtype : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    have hmap : (S : Subgroup L).map (L.normalizerMonoidHom (tN ^ 4)).toMonoidHom = S := by
      have hr : (S : Subgroup L) = ((S : Subgroup L).map q₀).comap q₀ := by
        rw [comap_map_eq,show q₀.ker = pCore 2 L from QuotientGroup.ker_mk' _,
          sup_eq_left.mpr (pCore_isPGroup.le_sylow_of_normal S)]
      ext x
      constructor
      · rintro ⟨y,hy,rfl⟩
        rw [hr]
        change q₀ (L.normalizerMonoidHom (tN ^ 4) y) ∈ (S : Subgroup L).map q₀
        rw [hq₀]
        exact mem_map_of_mem q₀ hy
      · intro hx
        refine ⟨(L.normalizerMonoidHom (tN ^ 4)).symm x,?_,(L.normalizerMonoidHom (tN ^ 4)).apply_symm_apply x⟩
        rw [hr]
        change q₀ ((L.normalizerMonoidHom (tN ^ 4)).symm x) ∈ (S : Subgroup L).map q₀
        rw [←hq₀ ((L.normalizerMonoidHom (tN ^ 4)).symm x),(L.normalizerMonoidHom (tN ^ 4)).apply_symm_apply]
        exact mem_map_of_mem q₀ hx
    have hm := congrArg (map L.subtype) hmap
    rw [map_map] at hm
    change (S : Subgroup L).map ((MulAut.conj (t ^ 4)).toMonoidHom.comp L.subtype) = _ at hm
    rwa [←map_map] at hm
  exact ((source_edge_local_normalizer h d hvz (.dihedral ⟨e⟩) S hS).1.le
    ⟨(stabilizer (family P) v).pow_mem ht.1 4,hNS⟩).2
end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial

namespace Matrix.SpecialLinearGroup
private theorem sylowNormalizer_le_of_fourth_powers
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (T : Sylow 2 SL(2,k)) (I : Subgroup SL(2,k)) (hTI : (T : Subgroup SL(2,k)) ≤ I)
    (h4 : ∀ g ∈ normalizer (T : Set SL(2,k)), g ^ 4 ∈ I) :
    normalizer (T : Set SL(2,k)) ≤ I := by
  let N := normalizer (T : Set SL(2,k))
  obtain ⟨f,hf,hker⟩ := exists_sylowNormalizer_diagonal (MonoidHom.id SL(2,k))
    Function.surjective_id T (by simp)
  let := Fintype.ofFinite k
  obtain ⟨n,_,hn⟩ := FiniteField.card k 2
  have hodd : Odd (Nat.card kˣ) := by
    rw [Nat.card_units,Nat.card_eq_fintype_card,hn]
    exact Nat.Even.sub_odd (Nat.one_le_two_pow (n := n))
      (even_two.pow_of_ne_zero (by exact n.ne_zero)) odd_one
  have hcop : (Nat.card kˣ).Coprime 4 := by
    simpa using hodd.coprime_two_right.pow_right 2
  intro g hg
  let x : N := ⟨g,hg⟩
  obtain ⟨u,hu⟩ := hcop.pow_left_bijective.surjective (f x)
  change u ^ 4 = f x at hu
  obtain ⟨y,hy⟩ := hf u
  have hdiff : ((x * (y ^ 4)⁻¹ : N) : SL(2,k)) ∈ T := by
    apply (hker _).mp
    rw [map_mul,map_inv,map_pow,hy,hu,mul_inv_cancel]
  have hm := I.mul_mem (hTI hdiff) (h4 y y.property)
  simpa only [Subgroup.coe_mul,Subgroup.coe_inv,Subgroup.coe_pow,inv_mul_cancel_right] using hm
end Matrix.SpecialLinearGroup

namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph CommutingTrivial
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
/-- A dihedral middle quotient still gives the full beta Borel: fourth powers cover its odd diagonal quotient. -/
theorem source_linear_path_borel_image_of_dihedral
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (d : EarlierLocalTheorems (family P))
    {beta mid a' : Vertex (family P)}
    (hbm : (graph (family P)).Adj beta mid)
    (ham : (graph (family P)).Adj a' mid)
    (hescape : ¬ Q (family P) mid ≤ Q (family P) beta)
    (em : (d.localGroup mid ⧸ pCore 2 (d.localGroup mid)) ≃* DihedralGroup 5)
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (e : (graphLocalGroup (family P) beta ⧸ pCore 2 (graphLocalGroup (family P) beta)) ≃*
      SL(2,k)) :
    let F := family P
    let L := graphLocalGroup F beta
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
    ∃ T : Sylow 2 SL(2,k), ((Q F mid).subgroupOf L).map q = T ∧
      ((stabilizer F mid ⊓ stabilizer F a').subgroupOf L).map q =
        normalizer (T : Set SL(2,k)) ∧
      ∀ l : L, q l ∈ normalizer (T : Set SL(2,k)) ↔ (l : G) • mid = mid := by
  let F := family P
  let L := graphLocalGroup F beta
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  let I := ((stabilizer F mid ⊓ stabilizer F a').subgroupOf L).map q
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨T,hT,hTf⟩ := linear_neighbor_core_sylow_image h hB hS hbm hescape e
  have hTI : (T : Subgroup SL(2,k)) ≤ I := by
    rw [←hT]
    apply map_mono
    exact comap_mono (le_inf (Q_le_stabilizer F mid)
      ((source_Z_Q_U h mid).2.trans ((ballKernel_one_le_edge F ham.symm).trans inf_le_right)))
  refine ⟨T,hT,le_antisymm ?_ ?_,hTf⟩
  · rintro _ ⟨x,hx,rfl⟩
    exact (hTf x).mpr hx.1
  · apply Matrix.SpecialLinearGroup.sylowNormalizer_le_of_fourth_powers T I hTI
    intro z hz
    obtain ⟨g,rfl⟩ := hq z
    have hgm : (g : G) ∈ stabilizer F mid := (hTf g).mp hz
    have hg4 := source_dihedral_edge_fourth_fixes_neighbors h hB d hbm.symm ham.symm
      em g ⟨hgm,sylowGenerated_le _ g.property⟩
    have hi : g ^ 4 ∈ (stabilizer F mid ⊓ stabilizer F a').subgroupOf L :=
      ⟨(stabilizer F mid).pow_mem hgm 4,hg4⟩
    simpa only [map_pow] using mem_map_of_mem q hi
end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
