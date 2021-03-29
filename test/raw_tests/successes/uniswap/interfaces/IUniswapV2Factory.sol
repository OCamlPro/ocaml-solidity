pragma solidity 0.7.0;

interface IUniswapV2Factory {
    event PairCreated(address indexed token0, address indexed token1, address pair, uint);

    function feeTo() external view returns (address);
    function feeToSetter() external view returns (address);

    function getPair(address tokenA, address tokenB) external view returns (address);
    function allPairs(uint) external view returns (address);
    function allPairsLength() external view returns (uint);

    function createPair(address tokenA, address tokenB) external returns (address);

    function setFeeTo(address) external;
    function setFeeToSetter(address) external;
}
