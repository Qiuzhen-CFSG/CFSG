module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.TerminalAction
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.TerminalKernel
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.TerminalDihedral
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.TerminalObstruction

/-!
# The constructed terminal module and its quadratic actor

In the long epsilon-two branch, construct the terminal edge, its literal
nonzero section V_t/Z_t, and the escaping radius-one actor. The actual
Sylow image generates this section from its fixed space. The same actor
is quadratic, has order greater than one and bounds its fixed-space index.
The last-odd path argument excludes an SL₂ quotient at this vertex.
Faithfulness on the actual Sylow subgroup and the same index bound also
exclude the D₁₀ quotient.

These conclusions prepare the actual module for the final contradiction.
Full faithfulness, residual fixed-space vanishing and the remaining model
comparison still require proof.
Source: DGS, *Groups and Graphs* (1985), (7.5), pp.129--131.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryConjugationSection Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition
open Subgroup.CosetGeometry.RankTwo
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
universe u
variable {G : Type u} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

theorem graph_epsilonTwo_terminal_module
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ x, Stellmacher.IsSylowSubgroupIn (Q (family P) x) (U (family P) x))
    (L : Vertex (family P) → Subgroup G)
    (hcov : ∀ g x, L (g • x) = (L x).map (MulAut.conj g).toMonoidHom)
    (d : ∀ x y, (graph (family P)).Adj x y →
      LocalRankOneData (stabilizer (family P) x)
        (stabilizer (family P) x ⊓ stabilizer (family P) y))
    (hstar : ∀ x y he, (d x y he).Pstar = L x)
    (hodd : ∀ x, ¬ 2 ∣ (L x).relIndex (stabilizer (family P) x))
    (hdich : ∀ x, Stellmacher.IsSylowSubgroupIn (Q (family P) x)
      (L x ⊓ centralizer (Z (family P) x : Set G)) ∨
      Z (family P) x = Stellmacher.omegaOneCenterAmbient (L x))
    (hob : ∀ x y, (graph (family P)).Adj x y → ¬ stabilizer (family P) y ≤ normalizer
      ((Q (family P) x ⊓ Q (family P) y : Subgroup G) : Set G))
    {v w u : Vertex (family P)} (hc : IsCriticalPair (family P) v w)
    (hne : ⁅Z (family P) v,Z (family P) w⁆ ≠ ⊥)
    (hvu : (graph (family P)).Adj v u)
    (hdu : (graph (family P)).dist u w + 1 = b (family P))
    (hepsilon : Z (family P) u = Stellmacher.omegaOneCenterAmbient
      ((stabilizer (family P) v ⊓ stabilizer (family P) u).pCoreIn 2))
    (hnat₀ : HasNaturalCenter (L v) (Z (family P) v) (Q (family P) v))
    (hnat₁ : HasNaturalCenter (L w) (Z (family P) w) (Q (family P) w))
    (hsyl : Stellmacher.IsSylowSubgroupIn
      (Z (family P) v ⊔ Q (family P) w) (stabilizer (family P) w))
    (hbranch : ∀ i, ∃ k, ((family P (!i)).subgroupOf (family P i)).index - 1 = 2^k)
    (hb : 2 < b (family P)) :
    ∃ t y : Vertex (family P), ∃ hty : (graph (family P)).Adj t y,
      let := finite_endpoints h
      let c := d t y hty
      letI : Finite c.Pstar := Finite.of_injective
        (inclusion c.Pstar_le) (inclusion_injective _)
      letI := graph_local_core_normal t c
      ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module (ZMod 2) W),
      ∃ σ : Representation (ZMod 2) (c.Pstar ⧸ (Q (family P) t).subgroupOf c.Pstar) W,
        Nonempty (BinaryConjugationSection c.Pstar (V (family P) t 1) (Z (family P) t)
          (σ.comp (QuotientGroup.mk' ((Q (family P) t).subgroupOf c.Pstar)))) ∧
        Nontrivial W ∧ Finite W ∧
        let π := QuotientGroup.mk' ((Q (family P) t).subgroupOf c.Pstar)
        let T := c.sylow.mapSurjective (QuotientGroup.mk'_surjective
          ((Q (family P) t).subgroupOf c.Pstar))
        GeneratedByFixedSpace σ T ∧ Disjoint σ.ker (T : Subgroup _) ∧
        (∃ a : Vertex (family P), (graph (family P)).Adj v a ∧
          V (family P) a 1 ≤ c.Pstar ∧
          let A := ((V (family P) a 1).subgroupOf c.Pstar).map π
          A ≤ T ∧ 1 < Nat.card A ∧ IsQuadratic σ A ∧
          Nat.card (W ⧸ fixedSpace σ A) ≤ Nat.card A) ∧
        ¬ Nonempty ((c.Pstar ⧸ (Q (family P) t).subgroupOf c.Pstar) ≃* DihedralGroup 5) ∧
        ∀ (k : Type u) (_ : Field k) (_ : Finite k) (_ : CharP k 2),
          ¬ Nonempty ((L t ⧸ pCore 2 (L t)) ≃* SL(2,k)) := by
  rcases graph_epsilonTwo_last_odd_not_linear h hB hS L hcov d hstar hodd hdich hob
    hc hne hvu hdu hepsilon hnat₀ hnat₁ hsyl hbranch with hb' |
      ⟨hbl,t,y,hwt,hty,hdt,hdy,hcore,hesc,hnot⟩
  · omega
  obtain ⟨u',a,x,hvu',hva,hu'a,hyx,hdu',hdx,ha⟩ :=
    graph_terminal_actor_configuration h hS hc hbl hwt hty hdy hesc
  have heps := graph_epsilonTwo_at_neighbor h hvu hvu' hepsilon
  let c := d t y hty
  let _ := graph_local_core_normal t c
  obtain ⟨W,hadd,hmodule,σ,⟨s⟩⟩ := graph_epsilonTwo_terminal_section_exists h hB hS L hcov
    d hstar hodd hdich hob hc hne hvu' hwt hdu' hdt heps hnat₀ hnat₁ hb hty
  let := hadd
  let := hmodule
  let := finite_endpoints h
  let : Finite c.Pstar := Finite.of_injective (inclusion c.Pstar_le) (inclusion_injective _)
  let : Finite (V (family P) t 1) := Finite.of_injective
    (inclusion s.section_le) (inclusion_injective _)
  have hfin : Finite W := Finite.of_surjective (fun z => (s.coordinates z).toAdd)
    (Multiplicative.toAdd.surjective.comp s.onto)
  have hnt := graph_terminal_section_nontrivial h hS hne hwt hdt s
  let π := QuotientGroup.mk' ((Q (family P) t).subgroupOf c.Pstar)
  let T := c.sylow.mapSurjective (QuotientGroup.mk'_surjective ((Q (family P) t).subgroupOf c.Pstar))
  let A := ((V (family P) a 1).subgroupOf c.Pstar).map π
  have hbnd := graph_epsilonTwo_terminal_section_bound h hB hS L hcov d hstar hodd hdich hob
    hc hne hvu' hwt hva hu'a hdu' hdt heps hnat₀ hnat₁ hsyl (by omega) hty hyx hdx hcore σ s
  have hAL : V (family P) a 1 ≤ c.Pstar := hbnd.1
  let : Finite (V (family P) a 1) := Finite.of_injective (inclusion hAL) (inclusion_injective _)
  have hE : ((stabilizer (family P) t ⊓ stabilizer (family P) y).pCoreIn 2).subgroupOf
      c.Pstar = c.sylow := by
    rw [←local_sylow_eq_edgeCore c (by rw [hstar]; exact hodd t)
      (source_edge_core_sylow h hB hty)]
    exact comap_map_eq_self_of_injective c.Pstar.subtype_injective _
  have hAS : A ≤ (T : Subgroup _) := by
    apply map_mono
    rw [←hE]
    exact subgroupOf_mono _ ((graph_V_adjacent_le hva 1).trans
      (hcore.trans (by simpa only [inf_comm] using graph_Q_le_edgeCore h hty.symm)))
  have hvw := (graph_epsilonTwo_even_of_localData h hB L hcov d hstar hodd hdich
    hc hne hvu hepsilon).1
  have htype : v.type = y.type := by
    have he := (same_orbit_iff (family P) v w).mp hvw
    have hw := hwt.1
    have hy := hty.1
    cases hv : v.type <;> cases hw' : w.type <;> cases ht : t.type <;>
      cases hy' : y.type <;> simp_all
  have hgen : GeneratedByFixedSpace σ T := by
    have he := graph_epsilonTwo_radius_section_generated_of_type h hB hvu hty.symm htype
      (d v u hvu) (d u v hvu.symm) c (by rw [hstar]; exact hodd v)
      (by rw [hstar]; exact hodd u) (by rw [hstar]; exact hdich u)
      hepsilon (by rw [hstar]; exact hnat₀) σ s
    rwa [hE] at he
  have hfaith : Disjoint σ.ker (T : Subgroup _) :=
    graph_epsilonTwo_terminal_sylow_kernel h hB hS hvu hty htype
      (d v u hvu) (by rw [hstar]; exact hodd v) hepsilon c.Pstar_le σ s c.sylow
  have hgt : 1 < Nat.card A := by
    rw [actor_image_card_eq_relIndex c.Pstar (Q (family P) t) _ π (QuotientGroup.ker_mk' _) hAL]
    exact Nat.one_lt_iff_ne_zero_and_ne_one.mpr
      ⟨index_ne_zero_of_finite,fun he => ha (relIndex_eq_one.mp he)⟩
  refine ⟨t,y,hty,W,hadd,hmodule,σ,⟨s⟩,hnt,hfin,hgen,hfaith,?_,?_,?_⟩
  · exact ⟨a,hva,hAL,hAS,hgt,hbnd.2⟩
  · rintro ⟨e⟩
    exact dihedral_fixed_generated_index_obstruction e σ T A hAS hgt hgen hfaith hbnd.2.2
  · intro k _ _ _
    exact (hnot k inferInstance inferInstance inferInstance).1

end CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
