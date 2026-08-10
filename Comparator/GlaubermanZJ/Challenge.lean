module

public import Comparator.GlaubermanZJ.Defs

namespace ZJ

public theorem glauberman_zj {G : Type*} [Group G] [IsSolvable G] (hodd : Odd (Nat.card G))
    {p : ℕ} [Fact p.Prime] (S : Sylow p G) :
    ((Subgroup.center (thompsonSubgroup S.toSubgroup)).map
        (thompsonSubgroup S.toSubgroup).subtype ⊔ pPrimeCore p G).Normal :=
  sorry

end ZJ
