module

public import CFSG.Quasithin.ChapterA.Section02.Sporadic.SourceAssembly.Common
public import CFSG.Quasithin.ChapterA.Section02.Sporadic.HaradaNorton
public import Theory.GroupTheory.PerfectCentralCoverQuasisimple
public import Theory.Alternating.OddCentralCovers
public import Theory.SpecificGroups.Alternating.QuasithinBounds

/-!
# The Harada–Norton proper-section exclusion

Pull the actual alternating-twelve subgroup back through the original central
projection and take its derived subgroup. The alternating odd-center theorem
makes this perfect central cover split trivially, so quasithin inheritance
contradicts the exact alternating degree bound.

Source: Aschbacher–Smith A.2.19, printed pp.40–41 (Case I and Case II).
-/

open Subgroup Theory.GroupTheory PerfectCentralCovering
namespace CFSG.Quasithin.ChapterA.Section02.Sporadic.SourceAssembly
universe u v
variable {G : Type u} {H : Type v} [Group G] [Finite G] [Group H]

public theorem not_quasithin_of_odd_central_a12
    (π : G →* H) (hπ : Function.Surjective π) (hc : π.ker ≤ center G)
    (ho : Odd (Nat.card π.ker))
    (j : alternatingGroup (Fin 12) →* H) (hj : Function.Injective j) :
    ¬ IsQuasithin G := by
  let A := alternatingGroup (Fin 12)
  let : IsSimpleGroup A := alternatingGroup.isSimpleGroup (by simp)
  have hna : ¬ IsMulCommutative A := by
    intro h
    have hh := alternatingGroup.isMulCommutative_iff_card_le_three.mp h
    simp at hh
  let : IsQuasisimple A := simple_quasisimple hna
  let R := j.range
  let N := R.comap π
  let ej : A ≃* R := MonoidHom.ofInjective hj
  let f : N →* A := ej.symm.toMonoidHom.comp (π.subgroupComap R)
  have hf : Function.Surjective f := ej.symm.surjective.comp
    (π.subgroupComap_surjective_of_surjective R hπ)
  have hfac (x : N) : j (f x) = π x := by
    exact congrArg Subtype.val (ej.apply_symm_apply (π.subgroupComap R x))
  have hfker : f.ker ≤ center N := by
    intro x hx
    have hxπ : π (x:G) = 1 := by rw [← hfac, hx, map_one]
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (mem_center_iff.mp (hc hxπ) (y:G))
  let D := commutator N
  let : Group.IsPerfect D := commutator_isPerfect_of_surjective_of_ker_le_center f hf hfker
  let fd : D →* A := f.comp D.subtype
  have hfd : Function.Surjective fd := by
    rw [← MonoidHom.range_eq_top]
    change (f.comp D.subtype).range = ⊤
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    change (commutator N).map f = ⊤
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hf]
    exact Group.IsPerfect.commutator_eq_top
  have hfdker : fd.ker ≤ center D := by
    intro x hx
    have hx' : (x:N) ∈ center N := hfker hx
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (mem_center_iff.mp hx' (y:N))
  let F : Cover D A := ⟨fd,hfd,inferInstance,hfdker⟩
  let : IsQuasisimple D := F.isQuasisimple
  have hZA : center A = ⊥ := center_eq_bot_of_simple hna
  let eD : D ⧸ center D ≃* A := F.quotientCenterEquiv.trans
    ((QuotientGroup.quotientMulEquivOfEq hZA).trans QuotientGroup.quotientBot)
  have hZker : center D = fd.ker := by
    simpa only [hZA, MonoidHom.comap_bot] using F.comap_center.symm
  let ι : center D →* π.ker := {
    toFun x := ⟨(((x:D):N):G), by
      change π ((((x:D):N):G)) = 1
      rw [← hfac]
      have hh : fd (x:D) = 1 := by
        change (x:D) ∈ fd.ker
        rw [← hZker]
        exact x.property
      rw [show f ((x:D):N) = 1 from hh,map_one]⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hι : Function.Injective ι := by
    intro x y h
    have hh : (((x:D):N):G) = (((y:D):N):G) :=
      congrArg (fun z : π.ker => (z:G)) h
    exact Subtype.ext (Subtype.ext (Subtype.ext hh))
  have hodd : Odd (Nat.card (center D)) := ho.of_dvd_nat
    (Subgroup.card_dvd_of_injective ι hι)
  have hcard : Nat.card (center D) = 1 :=
    (GLS3.Chapter5.OddCentralCovers.odd_center_alternatives 12 (by decide) eD hodd).resolve_right
      (by rintro ⟨h,_⟩; omega)
  let eDA : D ≃* A := GLS3.Chapter5.OddCentralCovers.alternatingEquivOfCenterCardOne 12 eD hcard
  intro hG
  have hA := Theory.GroupTheory.isQuasithin_of_equiv eDA ((hG.subgroup N).subgroup D)
  have hb := alternatingGroup.degree_le_nine_of_quasithin hA
  omega

public theorem not_quasithin_hn_cover (e : G ⧸ center G ≃* HaradaNorton.HN)
    (ho : Odd (Nat.card (center G))) : ¬ IsQuasithin G := by
  exact not_quasithin_of_odd_central_a12 (projection e) (projection_surjective e)
    (projection_ker e).le (by rwa [projection_ker])
    hn_properA12SubgroupData.embedding hn_properA12SubgroupData.injective

public theorem simple_hn (e : G ≃* HaradaNorton.HN) (hG : IsQuasithin G) : False := by
  let d := properA12SubgroupData_of_hn_equiv e
  have hA := isQuasithin_of_equiv (MonoidHom.ofInjective d.injective).symm
    (hG.subgroup d.embedding.range)
  have hb := alternatingGroup.degree_le_nine_of_quasithin hA
  omega

public theorem cover_hn [IsQuasisimple G] {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hP : IsPGroup p (center G)) (e : G ⧸ center G ≃* HaradaNorton.HN)
    (hG : IsQuasithin G) : False := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨n,hn⟩ := hP.exists_card_eq
  exact not_quasithin_hn_cover e (hn ▸ ho.pow) hG

end CFSG.Quasithin.ChapterA.Section02.Sporadic.SourceAssembly
