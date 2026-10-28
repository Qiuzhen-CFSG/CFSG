module
public import Theory.GroupAction.RankTwoCosetGeometry.Distance
public import Theory.GroupTheory.IntersectingConjugates
public import Theory.GroupTheory.SubgroupConjugation
/-!
# Commuting seeds in a coset geometry

Suppose each vertex group normalizes its seed and its seed centralizer fixes
the neighboring vertex. If intersecting seed conjugates commute, induction
along paths shows that all seed conjugates commute and fix every vertex.
The rank-two application retains the two original vertex subgroups.

A common abelian span under a point centralizer supplies the required mixed
commutation: move an intersection point to the distinguished point, then use
the normalizer transitivity of each seed to correct its transporter.

Source: the critical-pair argument in Aschbacher–Smith, 14.5.8, printed
p.1015, and A.1.7(1). The path induction avoids selecting a minimal pair
and requires neither finiteness nor a classification hypothesis.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G]

private theorem intersecting_normalized_commute {V W : Subgroup G}
    (hnV : V ≤ normalizer (W : Set G)) (hnW : W ≤ normalizer (V : Set G))
    (hc : V ⊓ W ≠ ⊥ → ⁅V,W⁆ = ⊥) : ⁅V,W⁆ = ⊥ := by
  by_cases h : V ⊓ W = ⊥
  · apply eq_bot_iff.mpr
    exact (le_inf (le_normalizer_iff_commutator_le_left.mp hnW)
      (le_normalizer_iff_commutator_le_right.mp hnV)).trans h.le
  · exact hc h

theorem seeds_propagate {Ω : Type*} (Γ : SimpleGraph Ω)
    (A N : Ω → Subgroup G)
    (hNA : ∀ v, N v ≤ A v)
    (hn : ∀ v, A v ≤ normalizer (N v : Set G))
    (hedge : ∀ v w, Γ.Adj v w → A v ⊓ centralizer (N v : Set G) ≤ A w)
    (hc : ∀ v w, N v ⊓ N w ≠ ⊥ → ⁅N v,N w⁆ = ⊥)
    {v w : Ω} (p : Γ.Walk v w) : N v ≤ A w ∧ ⁅N v,N w⁆ = ⊥ := by
  have all_paths : ∀ n, ∀ v w, ∀ p : Γ.Walk v w, p.length = n →
      N v ≤ A w ∧ ⁅N v,N w⁆ = ⊥ := by
    intro n
    induction n with
    | zero =>
      intro v w p hp
      have hvw : v = w := p.eq_of_length_eq_zero hp
      subst w
      exact ⟨hNA v,intersecting_normalized_commute ((hNA v).trans (hn v))
        ((hNA v).trans (hn v)) (hc v v)⟩
    | succ n ih =>
      have hrev : ∀ v w, ∀ p : Γ.Walk v w, p.length = n+1 → N w ≤ A v := by
        intro v w p hp
        cases p with
        | nil => simp at hp
        | @cons v t w hvt tail =>
          have ht : tail.length = n := by simpa using hp
          obtain ⟨hle,hcomm⟩ := ih w t tail.reverse (by simpa using ht)
          exact (le_inf hle (commutator_eq_bot_iff_le_centralizer.mp hcomm)).trans
            (hedge t v hvt.symm)
      intro v w p hp
      have hfor := hrev w v p.reverse (by simpa using hp)
      have hback := hrev v w p hp
      exact ⟨hfor,intersecting_normalized_commute (hfor.trans (hn w))
        (hback.trans (hn v)) (hc v w)⟩
  exact all_paths p.length v w p rfl
end Subgroup

namespace Subgroup.CosetGeometry.RankTwo
open Subgroup
variable {G : Type*} [Group G]
private def seedAt (F N : Bool → Subgroup G) (v : Vertex F) : Subgroup G :=
  ⨆ g : G, ⨆ (_ : g • base F v.type = v), (N v.type).conjBy g

private theorem seedAt_base (F N : Bool → Subgroup G)
    (hn : ∀ i, F i ≤ normalizer (N i : Set G)) (i : Bool) (g : G) :
    seedAt F N (g • base F i) = (N i).conjBy g := by
  apply le_antisymm
  · refine iSup_le fun h => iSup_le fun hh => ?_
    change h • base F i = g • base F i at hh
    have hm : g⁻¹*h ∈ F i := by
      rw [← CosetGeometry.stabilizer_base F i]
      change (g⁻¹*h) • base F i = base F i
      rw [mul_smul,hh,inv_smul_smul]
    have he := mem_normalizer_iff_map_conj_eq.mp (hn i hm)
    change (N i).conjBy (g⁻¹*h) = N i at he
    have hmap := congrArg (fun S : Subgroup G => S.conjBy g) he
    rw [←conjBy_mul] at hmap
    change (N i).conjBy h ≤ (N i).conjBy g
    simpa only [mul_inv_cancel_left] using hmap.le
  · exact le_iSup_of_le g (le_iSup_of_le rfl le_rfl)

/-- If intersecting seed conjugates commute and each local seed centralizer
fixes the other vertex, every seed conjugate fixes both base vertices. -/
theorem conjugate_seeds_in_overlap (F N : Bool → Subgroup G)
    (hgen : F false ⊔ F true = ⊤)
    (hle : ∀ i, N i ≤ F i)
    (hn : ∀ i, F i ≤ normalizer (N i : Set G))
    (hC : ∀ i j, i ≠ j → F i ⊓ centralizer (N i : Set G) ≤ F j)
    (hcomm : ∀ i j (g k : G), (N i).conjBy g ⊓ (N j).conjBy k ≠ ⊥ →
      ⁅(N i).conjBy g,(N j).conjBy k⁆ = ⊥) :
    (∀ i g, (N i).conjBy g ≤ F false ⊓ F true) ∧
      ∀ i j g k, ⁅(N i).conjBy g,(N j).conjBy k⁆ = ⊥ := by
  have hNA (v : Vertex F) : seedAt F N v ≤ stabilizer F v := by
    obtain ⟨g,hg⟩ := exists_smul_base F v
    rw [←hg,seedAt_base F N hn,stabilizer_translate]
    simp only [stabilizer,CosetGeometry.stabilizer_base]
    exact map_mono (hle _)
  have hnorm (v : Vertex F) : stabilizer F v ≤ normalizer (seedAt F N v : Set G) := by
    obtain ⟨g,hg⟩ := exists_smul_base F v
    rw [←hg,seedAt_base F N hn,stabilizer_translate]
    simp only [stabilizer,CosetGeometry.stabilizer_base]
    exact (map_mono (hn _)).trans (le_normalizer_map _)
  have hedge (v w : Vertex F) (hw : (graph F).Adj v w) :
      stabilizer F v ⊓ centralizer (seedAt F N v : Set G) ≤ stabilizer F w := by
    obtain ⟨g,hg,hg'⟩ := incident_common_translate F hw.2
    have ht := hw.1
    rw [←hg,←hg',seedAt_base F N hn,stabilizer_translate,stabilizer_translate,
      ]
    simp only [stabilizer,base,CosetGeometry.stabilizer_base]
    intro x hx
    have hxA : (MulAut.conj g⁻¹) x ∈ F v.type := by
      obtain ⟨a,ha,rfl⟩ := hx.1
      simpa [MulAut.conj_apply,mul_assoc] using ha
    have hxC : (MulAut.conj g⁻¹) x ∈ centralizer (N v.type : Set G) := by
      apply mem_centralizer_iff.mpr
      intro y hy
      have hh := mem_centralizer_iff.mp hx.2 ((MulAut.conj g) y) (mem_map_of_mem _ hy)
      apply (MulAut.conj g).injective
      simpa [MulAut.conj_apply,mul_assoc] using hh
    refine ⟨(MulAut.conj g⁻¹) x,hC _ _ ht ⟨hxA,hxC⟩,?_⟩
    simp [MulAut.conj_apply,mul_assoc]
  have hc (v w : Vertex F) : seedAt F N v ⊓ seedAt F N w ≠ ⊥ →
      ⁅seedAt F N v,seedAt F N w⁆ = ⊥ := by
    obtain ⟨g,hg⟩ := exists_smul_base F v
    obtain ⟨k,hk⟩ := exists_smul_base F w
    rw [←hg,←hk,seedAt_base F N hn,seedAt_base F N hn]
    exact hcomm _ _ _ _
  have hp (v w : Vertex F) : seedAt F N v ≤ stabilizer F w ∧
      ⁅seedAt F N v,seedAt F N w⁆ = ⊥ := by
    obtain ⟨p⟩ := (connected F hgen).preconnected v w
    exact Subgroup.seeds_propagate (graph F) (stabilizer F) (seedAt F N) hNA hnorm hedge hc p
  constructor
  · intro i g
    have ha := (hp (g • base F i) (base F false)).1
    have hb := (hp (g • base F i) (base F true)).1
    rw [seedAt_base F N hn] at ha hb
    simp only [stabilizer,base,CosetGeometry.stabilizer_base] at ha hb
    exact le_inf ha hb
  · intro i j g k
    simpa only [seedAt_base F N hn] using (hp (g • base F i) (k • base F j)).2
end Subgroup.CosetGeometry.RankTwo


namespace Subgroup
open scoped IsMulCommutative
variable {G : Type*} [Group G]

theorem mixed_intersection_commutes (V W U : Subgroup G) {z : G}
    (hz : z ≠ 1) (hVU : V ≤ U)
    (hWU : conjugateSpanBy W (centralizer ({z} : Set G)) ≤ U)
    [IsMulCommutative U]
    (hV : ∀ x ∈ V, x ≠ 1 → ∃ n ∈ normalizer (V : Set G), (MulAut.conj n) z = x)
    (hW : ∀ x ∈ W, x ≠ 1 → ∃ n ∈ normalizer (W : Set G), (MulAut.conj n) z = x)
    (g : G) (hg : V ⊓ W.map (MulAut.conj g).toMonoidHom ≠ ⊥) :
    ⁅V,W.map (MulAut.conj g).toMonoidHom⁆ = ⊥ := by
  obtain ⟨a,ha⟩ := ne_bot_iff_exists_ne_one.mp hg
  have hane : (a : G) ≠ 1 := fun he => ha (Subtype.ext he)
  obtain ⟨n,hn,hnz⟩ := hV a a.property.1 hane
  have hzW : z ∈ W.map (MulAut.conj (n⁻¹ * g)).toMonoidHom := by
    obtain ⟨b,hb,hba⟩ := a.property.2
    refine ⟨b,hb,?_⟩
    apply (MulAut.conj n).injective
    simpa [MulAut.conj_apply,mul_assoc] using hba.trans hnz.symm
  have hle : W.map (MulAut.conj (n⁻¹ * g)).toMonoidHom ≤ U := by
    have hh := conjugate_le_centralizerConjugateClosure W hz hW hzW
    rw [centralizerConjugateClosure_eq_conjugateSpanBy] at hh
    exact hh.trans hWU
  have hc : V ≤ centralizer (W.map (MulAut.conj (n⁻¹ * g)).toMonoidHom : Set G) :=
    hVU.trans ((le_centralizer U).trans (centralizer_le hle))
  apply commutator_eq_bot_iff_le_centralizer.mpr
  intro x hx
  apply mem_centralizer_iff.mpr
  intro y hy
  have hx' : (MulAut.conj n⁻¹) x ∈ V :=
    (mem_normalizer_iff.mp ((normalizer (V : Set G)).inv_mem hn) x).mp hx
  have hy' : (MulAut.conj n⁻¹) y ∈ W.map (MulAut.conj (n⁻¹ * g)).toMonoidHom := by
    obtain ⟨b,hb,rfl⟩ := hy
    refine ⟨b,hb,?_⟩
    simp [MulAut.conj_apply,mul_assoc]
  apply (MulAut.conj n⁻¹).injective
  simpa only [map_mul] using mem_centralizer_iff.mp (hc hx') _ hy'
end Subgroup

namespace Subgroup
variable {G : Type*} [Group G]
theorem mixed_conjugates_commute (V W : Subgroup G)
    (hc : ∀ g, V ⊓ W.conjBy g ≠ ⊥ → ⁅V,W.conjBy g⁆ = ⊥)
    (g k : G) (hi : V.conjBy g ⊓ W.conjBy k ≠ ⊥) :
    ⁅V.conjBy g,W.conjBy k⁆ = ⊥ := by
  have he : (W.conjBy (g⁻¹*k)).conjBy g = W.conjBy k := by
    rw [←conjBy_mul,mul_inv_cancel_left]
  have hn : V ⊓ W.conjBy (g⁻¹*k) ≠ ⊥ := by
    intro hz
    apply hi
    change V.map (MulAut.conj g).toMonoidHom ⊓ W.conjBy k = ⊥
    rw [←he,conjBy,←map_inf _ _ _ (MulAut.conj g).injective,hz,map_bot]
  have hh := congrArg (fun A : Subgroup G => A.map (MulAut.conj g).toMonoidHom) (hc (g⁻¹*k) hn)
  rw [map_commutator,map_bot] at hh
  change ⁅V.conjBy g,(W.conjBy (g⁻¹*k)).conjBy g⁆ = ⊥ at hh
  rwa [he] at hh
end Subgroup
