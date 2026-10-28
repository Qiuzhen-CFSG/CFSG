module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.InitialProducts.CheckArithmetic
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.InitialProducts.Scalar25

/-!
# Exact product checks on rows 1600 through 1663

Literal masks are connected to the published lists and packed XOR definitions.
The scalar checks therefore apply to precisely the original checker.
See source/README.md.
-/

set_option Elab.async false

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.LeftCertificate.InitialProducts
namespace Block25

private theorem t_raw : Wide.checkRows 1792 t RightCertificate.wideSecond tb = true := by
  apply product_cons_b t1600 tb1600 ts1600 _ _ ts1600_sum ts1600_parity
  apply product_cons_b t1601 tb1601 ts1601 _ _ ts1601_sum ts1601_parity
  apply product_cons_b t1602 tb1602 ts1602 _ _ ts1602_sum ts1602_parity
  apply product_cons_b t1603 tb1603 ts1603 _ _ ts1603_sum ts1603_parity
  apply product_cons_b t1604 tb1604 ts1604 _ _ ts1604_sum ts1604_parity
  apply product_cons_b t1605 tb1605 ts1605 _ _ ts1605_sum ts1605_parity
  apply product_cons_b t1606 tb1606 ts1606 _ _ ts1606_sum ts1606_parity
  apply product_cons_b t1607 tb1607 ts1607 _ _ ts1607_sum ts1607_parity
  apply product_cons_b t1608 tb1608 ts1608 _ _ ts1608_sum ts1608_parity
  apply product_cons_b t1609 tb1609 ts1609 _ _ ts1609_sum ts1609_parity
  apply product_cons_b t1610 tb1610 ts1610 _ _ ts1610_sum ts1610_parity
  apply product_cons_b t1611 tb1611 ts1611 _ _ ts1611_sum ts1611_parity
  apply product_cons_b t1612 tb1612 ts1612 _ _ ts1612_sum ts1612_parity
  apply product_cons_b t1613 tb1613 ts1613 _ _ ts1613_sum ts1613_parity
  apply product_cons_b t1614 tb1614 ts1614 _ _ ts1614_sum ts1614_parity
  apply product_cons_b t1615 tb1615 ts1615 _ _ ts1615_sum ts1615_parity
  apply product_cons_b t1616 tb1616 ts1616 _ _ ts1616_sum ts1616_parity
  apply product_cons_b t1617 tb1617 ts1617 _ _ ts1617_sum ts1617_parity
  apply product_cons_b t1618 tb1618 ts1618 _ _ ts1618_sum ts1618_parity
  apply product_cons_b t1619 tb1619 ts1619 _ _ ts1619_sum ts1619_parity
  apply product_cons_b t1620 tb1620 ts1620 _ _ ts1620_sum ts1620_parity
  apply product_cons_b t1621 tb1621 ts1621 _ _ ts1621_sum ts1621_parity
  apply product_cons_b t1622 tb1622 ts1622 _ _ ts1622_sum ts1622_parity
  apply product_cons_b t1623 tb1623 ts1623 _ _ ts1623_sum ts1623_parity
  apply product_cons_b t1624 tb1624 ts1624 _ _ ts1624_sum ts1624_parity
  apply product_cons_b t1625 tb1625 ts1625 _ _ ts1625_sum ts1625_parity
  apply product_cons_b t1626 tb1626 ts1626 _ _ ts1626_sum ts1626_parity
  apply product_cons_b t1627 tb1627 ts1627 _ _ ts1627_sum ts1627_parity
  apply product_cons_b t1628 tb1628 ts1628 _ _ ts1628_sum ts1628_parity
  apply product_cons_b t1629 tb1629 ts1629 _ _ ts1629_sum ts1629_parity
  apply product_cons_b t1630 tb1630 ts1630 _ _ ts1630_sum ts1630_parity
  apply product_cons_b t1631 tb1631 ts1631 _ _ ts1631_sum ts1631_parity
  apply product_cons_b t1632 tb1632 ts1632 _ _ ts1632_sum ts1632_parity
  apply product_cons_b t1633 tb1633 ts1633 _ _ ts1633_sum ts1633_parity
  apply product_cons_b t1634 tb1634 ts1634 _ _ ts1634_sum ts1634_parity
  apply product_cons_b t1635 tb1635 ts1635 _ _ ts1635_sum ts1635_parity
  apply product_cons_b t1636 tb1636 ts1636 _ _ ts1636_sum ts1636_parity
  apply product_cons_b t1637 tb1637 ts1637 _ _ ts1637_sum ts1637_parity
  apply product_cons_b t1638 tb1638 ts1638 _ _ ts1638_sum ts1638_parity
  apply product_cons_b t1639 tb1639 ts1639 _ _ ts1639_sum ts1639_parity
  apply product_cons_b t1640 tb1640 ts1640 _ _ ts1640_sum ts1640_parity
  apply product_cons_b t1641 tb1641 ts1641 _ _ ts1641_sum ts1641_parity
  apply product_cons_b t1642 tb1642 ts1642 _ _ ts1642_sum ts1642_parity
  apply product_cons_b t1643 tb1643 ts1643 _ _ ts1643_sum ts1643_parity
  apply product_cons_b t1644 tb1644 ts1644 _ _ ts1644_sum ts1644_parity
  apply product_cons_b t1645 tb1645 ts1645 _ _ ts1645_sum ts1645_parity
  apply product_cons_b t1646 tb1646 ts1646 _ _ ts1646_sum ts1646_parity
  apply product_cons_b t1647 tb1647 ts1647 _ _ ts1647_sum ts1647_parity
  apply product_cons_b t1648 tb1648 ts1648 _ _ ts1648_sum ts1648_parity
  apply product_cons_b t1649 tb1649 ts1649 _ _ ts1649_sum ts1649_parity
  apply product_cons_b t1650 tb1650 ts1650 _ _ ts1650_sum ts1650_parity
  apply product_cons_b t1651 tb1651 ts1651 _ _ ts1651_sum ts1651_parity
  apply product_cons_b t1652 tb1652 ts1652 _ _ ts1652_sum ts1652_parity
  apply product_cons_b t1653 tb1653 ts1653 _ _ ts1653_sum ts1653_parity
  apply product_cons_b t1654 tb1654 ts1654 _ _ ts1654_sum ts1654_parity
  apply product_cons_b t1655 tb1655 ts1655 _ _ ts1655_sum ts1655_parity
  apply product_cons_b t1656 tb1656 ts1656 _ _ ts1656_sum ts1656_parity
  apply product_cons_b t1657 tb1657 ts1657 _ _ ts1657_sum ts1657_parity
  apply product_cons_b t1658 tb1658 ts1658 _ _ ts1658_sum ts1658_parity
  apply product_cons_b t1659 tb1659 ts1659 _ _ ts1659_sum ts1659_parity
  apply product_cons_b t1660 tb1660 ts1660 _ _ ts1660_sum ts1660_parity
  apply product_cons_b t1661 tb1661 ts1661 _ _ ts1661_sum ts1661_parity
  apply product_cons_b t1662 tb1662 ts1662 _ _ ts1662_sum ts1662_parity
  apply product_cons_b t1663 tb1663 ts1663 _ _ ts1663_sum ts1663_parity
  rfl

private theorem d_raw : Wide.checkRows 1792 d RightCertificate.wideFirst da = true := by
  apply product_cons_a d1600 da1600 ds1600 _ _ ds1600_sum ds1600_parity
  apply product_cons_a d1601 da1601 ds1601 _ _ ds1601_sum ds1601_parity
  apply product_cons_a d1602 da1602 ds1602 _ _ ds1602_sum ds1602_parity
  apply product_cons_a d1603 da1603 ds1603 _ _ ds1603_sum ds1603_parity
  apply product_cons_a d1604 da1604 ds1604 _ _ ds1604_sum ds1604_parity
  apply product_cons_a d1605 da1605 ds1605 _ _ ds1605_sum ds1605_parity
  apply product_cons_a d1606 da1606 ds1606 _ _ ds1606_sum ds1606_parity
  apply product_cons_a d1607 da1607 ds1607 _ _ ds1607_sum ds1607_parity
  apply product_cons_a d1608 da1608 ds1608 _ _ ds1608_sum ds1608_parity
  apply product_cons_a d1609 da1609 ds1609 _ _ ds1609_sum ds1609_parity
  apply product_cons_a d1610 da1610 ds1610 _ _ ds1610_sum ds1610_parity
  apply product_cons_a d1611 da1611 ds1611 _ _ ds1611_sum ds1611_parity
  apply product_cons_a d1612 da1612 ds1612 _ _ ds1612_sum ds1612_parity
  apply product_cons_a d1613 da1613 ds1613 _ _ ds1613_sum ds1613_parity
  apply product_cons_a d1614 da1614 ds1614 _ _ ds1614_sum ds1614_parity
  apply product_cons_a d1615 da1615 ds1615 _ _ ds1615_sum ds1615_parity
  apply product_cons_a d1616 da1616 ds1616 _ _ ds1616_sum ds1616_parity
  apply product_cons_a d1617 da1617 ds1617 _ _ ds1617_sum ds1617_parity
  apply product_cons_a d1618 da1618 ds1618 _ _ ds1618_sum ds1618_parity
  apply product_cons_a d1619 da1619 ds1619 _ _ ds1619_sum ds1619_parity
  apply product_cons_a d1620 da1620 ds1620 _ _ ds1620_sum ds1620_parity
  apply product_cons_a d1621 da1621 ds1621 _ _ ds1621_sum ds1621_parity
  apply product_cons_a d1622 da1622 ds1622 _ _ ds1622_sum ds1622_parity
  apply product_cons_a d1623 da1623 ds1623 _ _ ds1623_sum ds1623_parity
  apply product_cons_a d1624 da1624 ds1624 _ _ ds1624_sum ds1624_parity
  apply product_cons_a d1625 da1625 ds1625 _ _ ds1625_sum ds1625_parity
  apply product_cons_a d1626 da1626 ds1626 _ _ ds1626_sum ds1626_parity
  apply product_cons_a d1627 da1627 ds1627 _ _ ds1627_sum ds1627_parity
  apply product_cons_a d1628 da1628 ds1628 _ _ ds1628_sum ds1628_parity
  apply product_cons_a d1629 da1629 ds1629 _ _ ds1629_sum ds1629_parity
  apply product_cons_a d1630 da1630 ds1630 _ _ ds1630_sum ds1630_parity
  apply product_cons_a d1631 da1631 ds1631 _ _ ds1631_sum ds1631_parity
  apply product_cons_a d1632 da1632 ds1632 _ _ ds1632_sum ds1632_parity
  apply product_cons_a d1633 da1633 ds1633 _ _ ds1633_sum ds1633_parity
  apply product_cons_a d1634 da1634 ds1634 _ _ ds1634_sum ds1634_parity
  apply product_cons_a d1635 da1635 ds1635 _ _ ds1635_sum ds1635_parity
  apply product_cons_a d1636 da1636 ds1636 _ _ ds1636_sum ds1636_parity
  apply product_cons_a d1637 da1637 ds1637 _ _ ds1637_sum ds1637_parity
  apply product_cons_a d1638 da1638 ds1638 _ _ ds1638_sum ds1638_parity
  apply product_cons_a d1639 da1639 ds1639 _ _ ds1639_sum ds1639_parity
  apply product_cons_a d1640 da1640 ds1640 _ _ ds1640_sum ds1640_parity
  apply product_cons_a d1641 da1641 ds1641 _ _ ds1641_sum ds1641_parity
  apply product_cons_a d1642 da1642 ds1642 _ _ ds1642_sum ds1642_parity
  apply product_cons_a d1643 da1643 ds1643 _ _ ds1643_sum ds1643_parity
  apply product_cons_a d1644 da1644 ds1644 _ _ ds1644_sum ds1644_parity
  apply product_cons_a d1645 da1645 ds1645 _ _ ds1645_sum ds1645_parity
  apply product_cons_a d1646 da1646 ds1646 _ _ ds1646_sum ds1646_parity
  apply product_cons_a d1647 da1647 ds1647 _ _ ds1647_sum ds1647_parity
  apply product_cons_a d1648 da1648 ds1648 _ _ ds1648_sum ds1648_parity
  apply product_cons_a d1649 da1649 ds1649 _ _ ds1649_sum ds1649_parity
  apply product_cons_a d1650 da1650 ds1650 _ _ ds1650_sum ds1650_parity
  apply product_cons_a d1651 da1651 ds1651 _ _ ds1651_sum ds1651_parity
  apply product_cons_a d1652 da1652 ds1652 _ _ ds1652_sum ds1652_parity
  apply product_cons_a d1653 da1653 ds1653 _ _ ds1653_sum ds1653_parity
  apply product_cons_a d1654 da1654 ds1654 _ _ ds1654_sum ds1654_parity
  apply product_cons_a d1655 da1655 ds1655 _ _ ds1655_sum ds1655_parity
  apply product_cons_a d1656 da1656 ds1656 _ _ ds1656_sum ds1656_parity
  apply product_cons_a d1657 da1657 ds1657 _ _ ds1657_sum ds1657_parity
  apply product_cons_a d1658 da1658 ds1658 _ _ ds1658_sum ds1658_parity
  apply product_cons_a d1659 da1659 ds1659 _ _ ds1659_sum ds1659_parity
  apply product_cons_a d1660 da1660 ds1660 _ _ ds1660_sum ds1660_parity
  apply product_cons_a d1661 da1661 ds1661 _ _ ds1661_sum ds1661_parity
  apply product_cons_a d1662 da1662 ds1662 _ _ ds1662_sum ds1662_parity
  apply product_cons_a d1663 da1663 ds1663 _ _ ds1663_sum ds1663_parity
  rfl

set_option maxRecDepth 8192 in
private theorem a_rows : ((Data1792.firstRows.toList).drop 1600).take 64 = a := by decide +kernel
set_option maxRecDepth 8192 in
private theorem b_rows : ((Data1792.secondRows.toList).drop 1600).take 64 = b := by decide +kernel
set_option maxRecDepth 8192 in
private theorem tb_rows : ((tbRows).drop 1600).take 64 = tb := by decide +kernel
set_option maxRecDepth 8192 in
private theorem da_rows : ((daRows).drop 1600).take 64 = da := by decide +kernel
private theorem t_xor : List.zipWith Nat.xor a b = t := by decide +kernel
private theorem d_xor : List.zipWith Nat.xor t tb = d := by decide +kernel
private theorem t_rows : (tRows.drop 1600).take 64 = t := by
  simp only [tRows, List.drop_zipWith, List.take_zipWith, a_rows, b_rows, t_xor]
private theorem d_rows : (dRows.drop 1600).take 64 = d := by
  simp only [dRows, List.drop_zipWith, List.take_zipWith, t_rows, tb_rows, d_xor]

theorem tb_checked : Wide.checkRows 1792 ((tRows.drop 1600).take 64) RightCertificate.wideSecond ((tbRows.drop 1600).take 64) = true := by
  rw [t_rows, tb_rows]
  exact t_raw

theorem da_checked : Wide.checkRows 1792 ((dRows.drop 1600).take 64) RightCertificate.wideFirst ((daRows.drop 1600).take 64) = true := by
  rw [d_rows, da_rows]
  exact d_raw


end Block25
end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.LeftCertificate.InitialProducts
